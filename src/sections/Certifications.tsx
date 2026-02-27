import { useEffect, useRef } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { Award, ExternalLink, ShieldCheck, Users } from 'lucide-react';
import { Button } from '@/components/ui/button';

gsap.registerPlugin(ScrollTrigger);

const certifications = [
  {
    title: 'SAFe® 6 Product Owner/Product Manager',
    issuer: 'Scaled Agile, Inc.',
    date: 'Issued February 2026',
    icon: ShieldCheck,
    color: '#E11D48',
    link: 'https://www.credly.com/earner/earned/badge/472d9477-f9e5-43e0-a881-bd73ac4e02f6',
    description: 'Certified professional capable of leading Agile teams, managing backlogs, and delivering value in a SAFe enterprise.',
    skills: ['Product Ownership', 'Backlog Refinement', 'Value Definition', 'Business Case Development']
  },
  {
    title: 'SAFe® 6 Scrum Master',
    issuer: 'Scaled Agile, Inc.',
    date: 'Issued February 2026',
    icon: Users,
    color: '#0EA5E9',
    link: 'https://www.credly.com/earner/earned/badge/472d9477-f9e5-43e0-a881-bd73ac4e02f6',
    description: 'Expertise in facilitating Scrum events, coaching teams on Agile principles, and removing impediments to delivery.',
    skills: ['Agile Methodologies', 'SAFe® Principles', 'Lean-Agile', 'Scaled Agile Framework®']
  }
];

export default function Certifications() {
  const sectionRef = useRef<HTMLElement>(null);
  const cardsRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const ctx = gsap.context(() => {
      if (cardsRef.current) {
        gsap.fromTo(
          cardsRef.current.children,
          { y: 50, opacity: 0 },
          {
            y: 0,
            opacity: 1,
            duration: 0.8,
            stagger: 0.2,
            ease: 'expo.out',
            scrollTrigger: {
              trigger: cardsRef.current,
              start: 'top 85%',
            },
          }
        );
      }
    }, sectionRef);

    return () => ctx.revert();
  }, []);

  return (
    <section
      ref={sectionRef}
      id="certifications"
      className="relative py-24 sm:py-32 overflow-hidden bg-background"
    >
      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        <div className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-primary mb-4 border border-primary/20">
            Credentials
          </span>
          <h2 className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight mb-4">
            Professional <span className="text-gradient">Certifications</span>
          </h2>
          <p className="text-lg text-muted-foreground max-w-2xl mx-auto">
            Certified in industry-standard methodologies to ensure delivery excellence and process efficiency.
          </p>
        </div>

        <div 
          ref={cardsRef}
          className="grid grid-cols-1 md:grid-cols-2 gap-8 max-w-5xl mx-auto"
        >
          {certifications.map((cert) => (
            <div
              key={cert.title}
              className="group relative glass p-8 rounded-3xl border hover:border-transparent transition-all duration-500 hover:-translate-y-2 overflow-hidden flex flex-col justify-between"
            >
              {/* Background Accent */}
              <div 
                className="absolute top-0 right-0 w-32 h-32 blur-[80px] opacity-10 group-hover:opacity-20 transition-opacity duration-500 rounded-full"
                style={{ backgroundColor: cert.color }}
              />

              <div>
                <div 
                  className="w-14 h-14 rounded-2xl flex items-center justify-center mb-6 transition-transform duration-500 group-hover:scale-110 group-hover:rotate-3 shadow-lg"
                  style={{ backgroundColor: `${cert.color}20`, color: cert.color }}
                >
                  <cert.icon size={28} />
                </div>
                
                <h3 className="text-2xl font-bold mb-2 group-hover:text-primary transition-colors">
                  {cert.title}
                </h3>
                <p className="text-sm font-semibold text-muted-foreground mb-4 flex items-center gap-2">
                  <Award size={14} className="text-primary" />
                  {cert.issuer} • {cert.date}
                </p>
                <p className="text-muted-foreground leading-relaxed mb-6">
                  {cert.description}
                </p>

                <div className="flex flex-wrap gap-2 mb-8">
                  {cert.skills.map((skill) => (
                    <span 
                      key={skill}
                      className="text-[10px] font-bold px-2 py-1 rounded-md bg-primary/5 border border-primary/10 text-muted-foreground transition-colors group-hover:text-primary group-hover:border-primary/20"
                    >
                      {skill}
                    </span>
                  ))}
                </div>
              </div>

              <div className="flex items-center justify-between pt-6 border-t border-border/50">
                <a 
                  href={cert.link} 
                  target="_blank" 
                  rel="noopener noreferrer"
                  className="inline-block"
                >
                  <Button 
                    variant="outline" 
                    className="rounded-full gap-2 border-primary/20 hover:bg-primary hover:text-white transition-all duration-300"
                  >
                    Verify Badge
                    <ExternalLink size={14} />
                  </Button>
                </a>
                <div 
                  className="text-xs font-black tracking-widest uppercase opacity-20 group-hover:opacity-40 transition-opacity"
                  style={{ color: cert.color }}
                >
                  SAFe® 6
                </div>
              </div>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}
