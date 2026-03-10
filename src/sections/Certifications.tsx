import { useEffect, useRef } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { Award, ExternalLink, ShieldCheck, Users } from 'lucide-react';
import { Button } from '@/components/ui/button';
import useEmblaCarousel from 'embla-carousel-react';
import Autoplay from 'embla-carousel-autoplay';

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
    skills: ['Agile Methodologies', 'Product Management', 'Backlog Management', 'Lean Agile', 'Business Ownership', 'PI Planning', 'Stakeholder Management', 'Value Stream Mapping', 'Roadmap Planning']
  },
  {
    title: 'SAFe® 6 Scrum Master',
    issuer: 'Scaled Agile, Inc.',
    date: 'Issued February 2026',
    icon: Users,
    color: '#0EA5E9',
    link: 'https://www.credly.com/earner/earned/badge/92697e6a-5110-4cca-a5c1-28793a715c9f',
    description: 'Expertise in facilitating Scrum events, coaching teams on Agile principles, and removing impediments to delivery.',
    skills: ['Agile Leadership', 'Agile Management', 'AI Prompting', 'Artificial General Intelligence', 'Business Coaching', 'Coach Agile Teams', 'Computer Programming', 'Kanban Principles', 'Leading Teams', 'Program Management', 'Scaled Agile Framework (SAFe)', 'Sprint Planning', 'Team Management', 'Servant Leadership', 'Facilitation', 'SDLC', 'Continuous Improvement']
  }
];

export default function Certifications() {
  const sectionRef = useRef<HTMLElement>(null);
  const [emblaRef] = useEmblaCarousel({ loop: true, align: 'start' }, [
    Autoplay({ delay: 4000, stopOnInteraction: false })
  ]);

  useEffect(() => {
    const ctx = gsap.context(() => {
      // Animation logic if needed
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

        {/* Carousel for Mobile, Grid for Desktop */}
        <div className="max-w-5xl mx-auto">
          {/* Mobile Carousel View */}
          <div className="block md:hidden">
            <div className="overflow-hidden" ref={emblaRef}>
              <div className="flex">
                {certifications.map((cert) => (
                  <div key={cert.title} className="flex-[0_0_100%] min-w-0 px-4">
                    <CertificationCard cert={cert} />
                  </div>
                ))}
              </div>
            </div>
          </div>

          {/* Desktop Grid View */}
          <div className="hidden md:grid grid-cols-2 gap-8">
            {certifications.map((cert) => (
              <CertificationCard key={cert.title} cert={cert} />
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}

function CertificationCard({ cert }: { cert: typeof certifications[0] }) {
  return (
    <div className="group relative glass p-8 rounded-3xl border hover:border-transparent transition-all duration-500 hover:-translate-y-2 overflow-hidden flex flex-col justify-between h-full">
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
  );
}

