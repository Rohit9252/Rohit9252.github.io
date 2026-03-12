import type { Metadata, Viewport } from "next";
import { Inter_Tight } from "next/font/google";
import "./globals.css";
import { ThemeProvider } from "../hooks/useTheme";

const interTight = Inter_Tight({
  subsets: ["latin"],
  weight: ["300", "400", "500", "600", "700", "800"],
  variable: "--font-inter-tight",
});

export const metadata: Metadata = {
  title: "Rohit Kumar | Backend Engineer & Software Developer",
  description: "Backend Engineer with 3+ years of experience building B2B SaaS backend systems in real estate (MLS) and fintech domains. Expert in Java, Spring Boot, MongoDB, AWS, and event-driven architectures.",
  keywords: "Rohit Kumar, Backend Engineer, Software Developer, Java, Spring Boot, MongoDB, AWS, Kafka, Microservices, Full Stack Developer, SAFe 6 Product Owner, SAFe 6 Scrum Master, Agile Methodologies, Bengaluru, India",
  authors: [{ name: "Rohit Kumar" }],
  robots: "index, follow",
  alternates: {
    canonical: "https://rohit9252.github.io/",
  },
  openGraph: {
    type: "website",
    url: "https://rohit9252.github.io/",
    title: "Rohit Kumar | Backend Engineer & Software Developer",
    description: "Backend Engineer with 3+ years of experience building B2B SaaS backend systems in real estate (MLS) and fintech domains.",
    images: [
      {
        url: "https://rohit9252.github.io/hero-portrait.jpg",
        width: 1200,
        height: 630,
        alt: "Rohit Kumar Portrait",
      },
    ],
    siteName: "Rohit Kumar Portfolio",
    locale: "en_US",
  },
  twitter: {
    card: "summary_large_image",
    title: "Rohit Kumar | Backend Engineer & Software Developer",
    description: "Backend Engineer with 3+ years of experience building B2B SaaS backend systems in real estate (MLS) and fintech domains.",
    images: ["https://rohit9252.github.io/hero-portrait.jpg"],
  },
};

export const viewport: Viewport = {
  themeColor: "#5B8DF7",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en" className="scroll-smooth">
      <head>
        <link rel="icon" type="image/svg+xml" href="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'><text y='.9em' font-size='90'>RK</text></svg>" />
        <script
          type="application/ld+json"
          dangerouslySetInnerHTML={{
            __html: JSON.stringify({
              "@context": "https://schema.org",
              "@type": "Person",
              "name": "Rohit Kumar",
              "jobTitle": "Backend Engineer",
              "description": "Backend Engineer with 3+ years of experience building B2B SaaS backend systems",
              "url": "https://rohit9252.github.io/",
              "email": "rohitbatra0165@gmail.com",
              "telephone": "+91-9056233995",
              "address": {
                "@type": "PostalAddress",
                "addressLocality": "Bengaluru",
                "addressRegion": "Karnataka",
                "addressCountry": "India"
              },
              "alumniOf": [
                {
                  "@type": "EducationalOrganization",
                  "name": "Masai School"
                },
                {
                  "@type": "EducationalOrganization",
                  "name": "Punjab University"
                }
              ],
              "worksFor": {
                "@type": "Organization",
                "name": "Noduco Software Private Limited"
              },
              "sameAs": [
                "https://linkedin.com/in/rohit-kumar",
                "https://github.com/rohit9252"
              ],
              "knowsAbout": [
                "Java",
                "Spring Boot",
                "MongoDB",
                "AWS",
                "Kafka",
                "Microservices",
                "Backend Development",
                "SAFe Framework",
                "Agile Management",
                "Product Management"
              ]
            }),
          }}
        />
      </head>
      <body className={`${interTight.variable} font-sans antialiased bg-background text-foreground`}>
        <ThemeProvider>
          {children}
        </ThemeProvider>
      </body>
    </html>
  );
}
