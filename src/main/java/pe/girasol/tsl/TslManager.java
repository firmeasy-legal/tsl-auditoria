package pe.girasol.tsl;

import eu.europa.esig.dss.enumerations.DigestAlgorithm;
import eu.europa.esig.dss.enumerations.SignatureLevel;
import eu.europa.esig.dss.enumerations.SignaturePackaging;
import eu.europa.esig.dss.model.DSSDocument;
import eu.europa.esig.dss.model.FileDocument;
import eu.europa.esig.dss.model.SignatureValue;
import eu.europa.esig.dss.model.ToBeSigned;
import eu.europa.esig.dss.token.DSSPrivateKeyEntry;
import eu.europa.esig.dss.token.Pkcs12SignatureToken;
import eu.europa.esig.dss.validation.CommonCertificateVerifier;
import eu.europa.esig.dss.validation.SignedDocumentValidator;
import eu.europa.esig.dss.validation.reports.Reports;
import eu.europa.esig.dss.xades.XAdESSignatureParameters;
import eu.europa.esig.dss.xades.signature.XAdESService;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathFactory;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.Console;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.KeyStore.PasswordProtection;
import java.security.MessageDigest;
import java.security.cert.CertificateFactory;
import java.security.cert.X509Certificate;
import java.time.Instant;
import java.time.format.DateTimeFormatter;
import java.time.temporal.ChronoUnit;
import java.util.Base64;
import java.util.HexFormat;

public class TslManager {

    private static final String TSL_NS = "http://uri.etsi.org/02231/v2#";
    private static final String DS_NS  = "http://www.w3.org/2000/09/xmldsig#";
    private static final String SVC_STATUS_UNDER_SUPERVISION =
            "http://uri.etsi.org/TrstSvc/eSigDir-1999-93-EC-TrustedList/Svcstatus/undersupervision";
    private static final String SVC_TYPE_CA_QC =
            "http://uri.etsi.org/TrstSvc/Svctype/CA/QC";

    private static final Console CONSOLE = System.console();
    private static final BufferedReader STDIN =
            new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));

    private static Path tslPath;
    private static String p12Path;
    private static char[] p12Password;

    // ============================================================
    // ENTRY POINT
    // ============================================================
    public static void main(String[] args) throws Exception {
        tslPath = Paths.get(args.length > 0 ? args[0] : "tsl2026.xml").toAbsolutePath();
        if (!Files.exists(tslPath)) {
            System.err.println("No se encontró la TSL: " + tslPath);
            System.err.println("Uso: tsl-manager [ruta-tsl.xml]");
            System.exit(1);
        }

        System.out.println("=====================================");
        System.out.println(" TSL Manager (DSS XAdES)");
        System.out.println("=====================================");
        System.out.println("Archivo TSL: " + tslPath);

        while (true) {
            System.out.println();
            System.out.println("1) Listar providers");
            System.out.println("2) Añadir certificado a un provider");
            System.out.println("3) Eliminar certificado de un provider");
            System.out.println("4) Verificar firma XAdES");
            System.out.println("5) Cambiar firmante (olvidar PKCS#12 de la sesión)");
            System.out.println("0) Salir");
            String opt = prompt("=> ").trim();
            try {
                switch (opt) {
                    case "1": listProviders(); break;
                    case "2": addCertToProvider(); break;
                    case "3": removeCertFromProvider(); break;
                    case "4": verifySignature(); break;
                    case "5": forgetSigner(); break;
                    case "0": case "q": case "exit": return;
                    default: System.out.println("Opción inválida.");
                }
            } catch (Exception e) {
                System.out.println("ERROR: " + e.getMessage());
            }
        }
    }

    // ============================================================
    // COMMAND 1 — LIST PROVIDERS
    // ============================================================
    private static void listProviders() throws Exception {
        Document doc = parse(tslPath.toFile());
        NodeList tsps = xpathList(doc, "//*[local-name()='TrustServiceProvider']");
        System.out.println();
        System.out.println("Providers en la TSL:");
        for (int i = 0; i < tsps.getLength(); i++) {
            Element tsp = (Element) tsps.item(i);
            String name  = textAt(tsp, ".//*[local-name()='TSPName']/*[local-name()='Name']");
            String trade = textAt(tsp, ".//*[local-name()='TSPTradeName']/*[local-name()='Name']");
            NodeList svcs = xpathList(tsp, ".//*[local-name()='TSPService']");
            System.out.printf("  %2d) %s%s  [%d servicio(s)]%n",
                    i + 1, name,
                    trade != null ? "  (" + trade + ")" : "",
                    svcs.getLength());
        }
    }

    // ============================================================
    // COMMAND 2 — ADD CERTIFICATE TO PROVIDER
    // ============================================================
    private static void addCertToProvider() throws Exception {
        Document doc = parse(tslPath.toFile());
        removeExistingSignature(doc);

        Element tspList = (Element) xpathNode(doc, "//*[local-name()='TrustServiceProviderList']");
        if (tspList == null) throw new IllegalStateException("TrustServiceProviderList no encontrado");

        NodeList tsps = xpathList(doc, "//*[local-name()='TrustServiceProvider']");
        System.out.println();
        System.out.println("Providers disponibles:");
        for (int i = 0; i < tsps.getLength(); i++) {
            Element tsp = (Element) tsps.item(i);
            String name = textAt(tsp, ".//*[local-name()='TSPName']/*[local-name()='Name']");
            System.out.printf("  %2d) %s%n", i + 1, name);
        }
        System.out.println("   n) Crear nuevo provider");

        String choice = prompt("Elige provider: ").trim();
        Element tsp;
        if (choice.equalsIgnoreCase("n")) {
            String name = prompt("Nombre del nuevo provider (TSPName): ").trim();
            if (name.isEmpty()) { System.out.println("Cancelado."); return; }
            tsp = createMinimalTsp(doc, name);
            tspList.appendChild(tsp);
            System.out.println("(Provider mínimo creado. Recuerda completar TSPInformation a mano si aplica.)");
        } else {
            int idx = parseIndex(choice, tsps.getLength());
            if (idx < 0) return;
            tsp = (Element) tsps.item(idx);
        }

        String certPath = prompt("Ruta del certificado (.pem/.der/.crt): ").trim();
        if (certPath.isEmpty()) { System.out.println("Cancelado."); return; }

        X509Certificate cert = loadCertificate(new File(certPath));
        byte[] der = cert.getEncoded();
        String cn  = commonName(cert);

        System.out.println("Certificado leído:");
        System.out.println("  Subject : " + cert.getSubjectX500Principal().getName());
        System.out.println("  Serial  : " + cert.getSerialNumber().toString(16));
        System.out.println("  SHA-256 : " + sha256Hex(der));

        String svcName = prompt("Nombre del servicio (ServiceName) [" + cn + "]: ").trim();
        if (svcName.isEmpty()) svcName = cn;

        Element services = (Element) xpathNode(tsp, "./*[local-name()='TSPServices']");
        if (services == null) {
            services = doc.createElementNS(TSL_NS, "tsl:TSPServices");
            tsp.appendChild(services);
        }
        services.appendChild(buildService(doc, cert, der, svcName));
        System.out.println("Certificado añadido. Procediendo a firmar...");

        signAndSave(doc);
    }

    // ============================================================
    // COMMAND 3 — REMOVE CERTIFICATE FROM PROVIDER
    // ============================================================
    private static void removeCertFromProvider() throws Exception {
        Document doc = parse(tslPath.toFile());
        removeExistingSignature(doc);

        NodeList tsps = xpathList(doc, "//*[local-name()='TrustServiceProvider']");
        if (tsps.getLength() == 0) { System.out.println("No hay providers."); return; }

        System.out.println();
        System.out.println("Providers:");
        for (int i = 0; i < tsps.getLength(); i++) {
            Element tsp = (Element) tsps.item(i);
            String name = textAt(tsp, ".//*[local-name()='TSPName']/*[local-name()='Name']");
            NodeList svcs = xpathList(tsp, ".//*[local-name()='TSPService']");
            System.out.printf("  %2d) %s  [%d servicio(s)]%n", i + 1, name, svcs.getLength());
        }
        int tspIdx = parseIndex(prompt("Elige provider: ").trim(), tsps.getLength());
        if (tspIdx < 0) return;
        Element tsp = (Element) tsps.item(tspIdx);

        NodeList svcs = xpathList(tsp, ".//*[local-name()='TSPService']");
        if (svcs.getLength() == 0) { System.out.println("(provider sin servicios)"); return; }

        System.out.println();
        System.out.println("Servicios / certificados del provider:");
        for (int i = 0; i < svcs.getLength(); i++) {
            Element svc = (Element) svcs.item(i);
            String svcName = textAt(svc, ".//*[local-name()='ServiceName']/*[local-name()='Name']");
            System.out.printf("  %2d) %s%n", i + 1, svcName);
            NodeList certs = xpathList(svc, ".//*[local-name()='DigitalId']/*[local-name()='X509Certificate']");
            for (int j = 0; j < certs.getLength(); j++) {
                String b64 = certs.item(j).getTextContent().replaceAll("\\s+", "");
                try {
                    byte[] der = Base64.getDecoder().decode(b64);
                    X509Certificate x = certFromBytes(der);
                    System.out.println("       Subject : " + x.getSubjectX500Principal().getName());
                    System.out.println("       SHA-256 : " + sha256Hex(der));
                } catch (Exception e) {
                    System.out.println("       [cert no parseable]");
                }
            }
        }
        int svcIdx = parseIndex(prompt("Elige servicio a eliminar: ").trim(), svcs.getLength());
        if (svcIdx < 0) return;

        Element toRemove = (Element) svcs.item(svcIdx);
        toRemove.getParentNode().removeChild(toRemove);
        System.out.println("Servicio eliminado.");

        NodeList remaining = xpathList(tsp, ".//*[local-name()='TSPService']");
        if (remaining.getLength() == 0) {
            String rm = prompt("El provider quedó sin servicios. ¿Eliminar provider también? [s/N]: ").trim();
            if (rm.equalsIgnoreCase("s") || rm.equalsIgnoreCase("si") || rm.equalsIgnoreCase("y")) {
                tsp.getParentNode().removeChild(tsp);
                System.out.println("Provider eliminado.");
            }
        }

        System.out.println("Procediendo a firmar...");
        signAndSave(doc);
    }

    // ============================================================
    // COMMAND 4 — VERIFY SIGNATURE
    // ============================================================
    private static void verifySignature() throws Exception {
        DSSDocument signed = new FileDocument(tslPath.toFile());
        SignedDocumentValidator validator = SignedDocumentValidator.fromDocument(signed);
        validator.setCertificateVerifier(new CommonCertificateVerifier());
        Reports reports = validator.validateDocument();

        System.out.println();
        System.out.println("=== Resumen de firma(s) XAdES ===");
        if (reports.getDiagnosticData().getSignatures().isEmpty()) {
            System.out.println("No se encontraron firmas en el documento.");
            return;
        }
        reports.getDiagnosticData().getSignatures().forEach(s -> {
            System.out.println("Signature id   : " + s.getId());
            System.out.println("  Format       : " + s.getSignatureFormat());
            System.out.println("  Signing cert : " + (s.getSigningCertificate() != null
                    ? s.getSigningCertificate().getCommonName() : "-"));
            System.out.println("  Signing time : " + s.getClaimedSigningTime());
            System.out.println("  Digest OK    : " + s.isSignatureIntact());
            System.out.println("  Signature OK : " + s.isSignatureValid());
            System.out.println("  B-Level OK   : " + s.isBLevelTechnicallyValid());
        });
    }

    // ============================================================
    // COMMAND 5 — FORGET SIGNER
    // ============================================================
    private static void forgetSigner() {
        p12Path = null;
        if (p12Password != null) java.util.Arrays.fill(p12Password, '\0');
        p12Password = null;
        System.out.println("Credenciales de firma olvidadas.");
    }

    // ============================================================
    // SIGNING (XAdES_BASELINE_B enveloped) + SAVE IN PLACE
    // ============================================================
    private static void signAndSave(Document doc) throws Exception {
        removeExistingSignature(doc);

        File tmp = File.createTempFile("tsl-unsigned-", ".xml");
        try {
            write(doc, tmp);

            if (p12Path == null || p12Password == null) {
                System.out.println();
                System.out.println("Firmante PKCS#12 (se recordará durante esta sesión):");
                p12Path = prompt("  Ruta .p12 / .pfx: ").trim();
                p12Password = promptPassword("  Password: ");
            }

            try (Pkcs12SignatureToken token = new Pkcs12SignatureToken(
                    p12Path, new PasswordProtection(p12Password))) {

                DSSPrivateKeyEntry key = token.getKeys().get(0);

                XAdESSignatureParameters params = new XAdESSignatureParameters();
                params.setSignatureLevel(SignatureLevel.XAdES_BASELINE_B);
                params.setSignaturePackaging(SignaturePackaging.ENVELOPED);
                params.setDigestAlgorithm(DigestAlgorithm.SHA256);
                params.setSigningCertificate(key.getCertificate());
                params.setCertificateChain(key.getCertificateChain());
                params.setEn319132(false); // ETSI TS 119 612: XAdES 1.3.2 clásico

                DSSDocument in = new FileDocument(tmp);
                XAdESService service = new XAdESService(new CommonCertificateVerifier());
                ToBeSigned dataToSign = service.getDataToSign(in, params);
                SignatureValue sig = token.sign(dataToSign, params.getDigestAlgorithm(), key);
                DSSDocument signed = service.signDocument(in, params, sig);

                try (InputStream is = signed.openStream()) {
                    Files.copy(is, tslPath, StandardCopyOption.REPLACE_EXISTING);
                }
                System.out.println("TSL firmada y guardada -> " + tslPath);
                System.out.println("Firmante: " + key.getCertificate().getSubject().getRFC2253());
            } catch (Exception e) {
                // si la firma falló, olvidamos las credenciales para no repetirlas mal
                forgetSigner();
                throw e;
            }
        } finally {
            //noinspection ResultOfMethodCallIgnored
            tmp.delete();
        }
    }

    // ============================================================
    // TSL BUILDERS
    // ============================================================
    private static Element createMinimalTsp(Document doc, String tspName) {
        Element tsp = doc.createElementNS(TSL_NS, "tsl:TrustServiceProvider");
        Element info = doc.createElementNS(TSL_NS, "tsl:TSPInformation");

        info.appendChild(wrappedName(doc, "tsl:TSPName", tspName));
        info.appendChild(wrappedName(doc, "tsl:TSPTradeName", tspName));

        Element addr = doc.createElementNS(TSL_NS, "tsl:TSPAddress");
        Element postals = doc.createElementNS(TSL_NS, "tsl:PostalAddresses");
        Element postal = doc.createElementNS(TSL_NS, "tsl:PostalAddress");
        postal.setAttribute("xml:lang", "es");
        postal.appendChild(el(doc, "tsl:StreetAddress", "-"));
        postal.appendChild(el(doc, "tsl:Locality", "-"));
        postal.appendChild(el(doc, "tsl:StateOrProvince", "-"));
        postal.appendChild(el(doc, "tsl:PostalCode", "-"));
        postal.appendChild(el(doc, "tsl:CountryName", "PE"));
        postals.appendChild(postal);
        addr.appendChild(postals);
        Element elec = doc.createElementNS(TSL_NS, "tsl:ElectronicAddress");
        elec.appendChild(el(doc, "tsl:URI", "-"));
        addr.appendChild(elec);
        info.appendChild(addr);

        Element infoUri = doc.createElementNS(TSL_NS, "tsl:TSPInformationURI");
        Element uri = doc.createElementNS(TSL_NS, "tsl:URI");
        uri.setAttribute("xml:lang", "en");
        uri.setTextContent("-");
        infoUri.appendChild(uri);
        info.appendChild(infoUri);

        tsp.appendChild(info);
        tsp.appendChild(doc.createElementNS(TSL_NS, "tsl:TSPServices"));
        return tsp;
    }

    private static Element buildService(Document doc, X509Certificate cert, byte[] der, String serviceName) {
        Element svc = doc.createElementNS(TSL_NS, "tsl:TSPService");
        Element info = doc.createElementNS(TSL_NS, "tsl:ServiceInformation");

        info.appendChild(el(doc, "tsl:ServiceTypeIdentifier", SVC_TYPE_CA_QC));
        info.appendChild(wrappedName(doc, "tsl:ServiceName", serviceName));

        Element sdi = doc.createElementNS(TSL_NS, "tsl:ServiceDigitalIdentity");
        sdi.appendChild(digitalId(doc, "tsl:X509Certificate", Base64.getEncoder().encodeToString(der)));
        sdi.appendChild(digitalId(doc, "tsl:X509SubjectName",
                cert.getSubjectX500Principal().getName()));
        String ski = encodeSkiAsInTsl(cert);
        if (ski != null) sdi.appendChild(digitalId(doc, "tsl:X509SKI", ski));
        info.appendChild(sdi);

        info.appendChild(el(doc, "tsl:ServiceStatus", SVC_STATUS_UNDER_SUPERVISION));
        info.appendChild(el(doc, "tsl:StatusStartingTime",
                DateTimeFormatter.ISO_INSTANT.format(Instant.now().truncatedTo(ChronoUnit.MILLIS))));

        svc.appendChild(info);
        svc.appendChild(doc.createElementNS(TSL_NS, "tsl:ServiceHistory"));
        return svc;
    }

    private static Element wrappedName(Document doc, String wrapperQname, String value) {
        Element w = doc.createElementNS(TSL_NS, wrapperQname);
        Element n = doc.createElementNS(TSL_NS, "tsl:Name");
        n.setAttribute("xml:lang", "en");
        n.setTextContent(value);
        w.appendChild(n);
        return w;
    }

    private static Element digitalId(Document doc, String childQname, String value) {
        Element did = doc.createElementNS(TSL_NS, "tsl:DigitalId");
        did.appendChild(el(doc, childQname, value));
        return did;
    }

    private static Element el(Document doc, String qname, String text) {
        Element e = doc.createElementNS(TSL_NS, qname);
        e.setTextContent(text);
        return e;
    }

    // ============================================================
    // CERT HELPERS
    // ============================================================
    private static X509Certificate loadCertificate(File f) throws Exception {
        if (!f.exists()) throw new IOException("No existe: " + f);
        try (InputStream is = Files.newInputStream(f.toPath())) {
            return (X509Certificate) CertificateFactory.getInstance("X.509").generateCertificate(is);
        }
    }

    private static X509Certificate certFromBytes(byte[] der) throws Exception {
        return (X509Certificate) CertificateFactory.getInstance("X.509")
                .generateCertificate(new ByteArrayInputStream(der));
    }

    private static String commonName(X509Certificate cert) {
        String dn = cert.getSubjectX500Principal().getName();
        for (String rdn : dn.split(",")) {
            String t = rdn.trim();
            if (t.toUpperCase().startsWith("CN=")) return t.substring(3);
        }
        return dn;
    }

    // El TSL peruano guarda X509SKI como base64(base64(rawSki)). Matcheamos esa convención.
    private static String encodeSkiAsInTsl(X509Certificate cert) {
        byte[] ski = extractRawSki(cert);
        if (ski == null) return null;
        String innerB64 = Base64.getEncoder().encodeToString(ski);
        return Base64.getEncoder().encodeToString(innerB64.getBytes(StandardCharsets.US_ASCII));
    }

    private static byte[] extractRawSki(X509Certificate cert) {
        byte[] ext = cert.getExtensionValue("2.5.29.14");
        if (ext == null || ext.length < 4) return null;
        try {
            int idx = 0;
            if (ext[idx++] != 0x04) return null;
            Len outer = readLen(ext, idx); idx += outer.consumed;
            if (ext[idx++] != 0x04) return null;
            Len inner = readLen(ext, idx); idx += inner.consumed;
            byte[] ski = new byte[inner.value];
            System.arraycopy(ext, idx, ski, 0, inner.value);
            return ski;
        } catch (Exception e) { return null; }
    }

    private record Len(int value, int consumed) {}
    private static Len readLen(byte[] b, int off) {
        int first = b[off] & 0xFF;
        if ((first & 0x80) == 0) return new Len(first, 1);
        int n = first & 0x7F;
        int v = 0;
        for (int i = 1; i <= n; i++) v = (v << 8) | (b[off + i] & 0xFF);
        return new Len(v, 1 + n);
    }

    private static String sha256Hex(byte[] der) {
        try { return HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(der)); }
        catch (Exception e) { throw new RuntimeException(e); }
    }

    // ============================================================
    // XML HELPERS
    // ============================================================
    private static void removeExistingSignature(Document doc) throws Exception {
        NodeList sigs = xpathList(doc,
                "/*[local-name()='TrustServiceStatusList']" +
                "/*[local-name()='Signature' and namespace-uri()='" + DS_NS + "']");
        for (int i = sigs.getLength() - 1; i >= 0; i--) {
            Node s = sigs.item(i);
            s.getParentNode().removeChild(s);
        }
    }

    private static Node xpathNode(Node ctx, String expr) throws Exception {
        return (Node) XPathFactory.newInstance().newXPath().evaluate(expr, ctx, XPathConstants.NODE);
    }

    private static NodeList xpathList(Node ctx, String expr) throws Exception {
        return (NodeList) XPathFactory.newInstance().newXPath().evaluate(expr, ctx, XPathConstants.NODESET);
    }

    private static String textAt(Node ctx, String expr) throws Exception {
        Node n = xpathNode(ctx, expr);
        return n == null ? null : n.getTextContent().trim();
    }

    private static Document parse(File f) throws Exception {
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setNamespaceAware(true);
        dbf.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
        DocumentBuilder db = dbf.newDocumentBuilder();
        return db.parse(f);
    }

    private static void write(Document doc, File out) throws Exception {
        Transformer t = TransformerFactory.newInstance().newTransformer();
        t.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
        t.setOutputProperty(OutputKeys.INDENT, "no");
        t.transform(new DOMSource(doc), new StreamResult(out));
    }

    // ============================================================
    // INPUT HELPERS
    // ============================================================
    private static String prompt(String msg) throws IOException {
        if (CONSOLE != null) {
            String s = CONSOLE.readLine(msg);
            return s == null ? "" : s;
        }
        System.out.print(msg);
        String s = STDIN.readLine();
        return s == null ? "" : s;
    }

    private static char[] promptPassword(String msg) throws IOException {
        if (CONSOLE != null) {
            char[] c = CONSOLE.readPassword(msg);
            return c == null ? new char[0] : c;
        }
        System.out.print(msg + "(aviso: sin consola TTY, se mostrará al escribir) ");
        String s = STDIN.readLine();
        return s == null ? new char[0] : s.toCharArray();
    }

    private static int parseIndex(String s, int size) {
        try {
            int i = Integer.parseInt(s) - 1;
            if (i < 0 || i >= size) { System.out.println("Índice fuera de rango."); return -1; }
            return i;
        } catch (NumberFormatException e) {
            System.out.println("Opción inválida.");
            return -1;
        }
    }
}
