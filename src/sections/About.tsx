import { useEffect, useRef } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { Briefcase, Code,  Layers } from 'lucide-react';

gsap.registerPlugin(ScrollTrigger);

const stats = [
  { icon: Briefcase, value: '3+', label: 'Years Experience' },
  { icon: Code, value: '15+', label: 'Java Projects' },
  { icon: Layers, value: '30+', label: 'Zoho Implementations' },
  // { icon: Database, value: '100K+', label: 'Records Processed' },
  // { icon: Award, value: '600+', label: 'DSA Problems Solved' },
  // { icon: Zap, value: '10+', label: 'Enterprise Clients' },
];

const highlights = [
  'Agentic AI & Generative AI',
  'Java & Spring Boot Expert',
  'Python Development',
  'SAFe® 6 Certified',
  'Lean-Agile Mindset',
  'Product Ownership',
  'Agile Methodologies',
  'MongoDB & AWS Specialist',
  'Microservices Design',
  'Enterprise Automation',
];

export default function About() {
  const sectionRef = useRef<HTMLElement>(null);
  const headingRef = useRef<HTMLHeadingElement>(null);
  const contentRef = useRef<HTMLDivElement>(null);
  const statsRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const ctx = gsap.context(() => {
      // Heading animation
      gsap.fromTo(
        headingRef.current,
        { y: 50, opacity: 0 },
        {
          y: 0,
          opacity: 1,
          duration: 0.8,
          ease: 'expo.out',
          scrollTrigger: {
            trigger: headingRef.current,
            start: 'top 80%',
            toggleActions: 'play none none reverse',
          },
        }
      );

      // Content paragraphs animation
      const paragraphs = contentRef.current?.querySelectorAll('p');
      if (paragraphs) {
        gsap.fromTo(
          paragraphs,
          { y: 30, opacity: 0 },
          {
            y: 0,
            opacity: 1,
            duration: 0.6,
            stagger: 0.1,
            ease: 'expo.out',
            scrollTrigger: {
              trigger: contentRef.current,
              start: 'top 70%',
              toggleActions: 'play none none reverse',
            },
          }
        );
      }

      // Stats animation
      const statItems = statsRef.current?.querySelectorAll('.stat-item');
      if (statItems) {
        gsap.fromTo(
          statItems,
          { y: 40, opacity: 0, scale: 0.9 },
          {
            y: 0,
            opacity: 1,
            scale: 1,
            duration: 0.6,
            stagger: 0.1,
            ease: 'expo.out',
            scrollTrigger: {
              trigger: statsRef.current,
              start: 'top 80%',
              toggleActions: 'play none none reverse',
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
      id="about"
      className="relative py-24 sm:py-32 overflow-hidden"
    >
      {/* Background elements */}
      <div className="absolute inset-0 pointer-events-none">
        <div className="absolute top-0 right-0 w-1/2 h-full bg-gradient-to-l from-[#5B8DF7]/5 to-transparent" />
        <div className="absolute bottom-0 left-0 w-96 h-96 bg-purple-500/5 rounded-full blur-3xl" />
      </div>

      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        {/* Section Header */}
        <div className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-[#5B8DF7] mb-4">
            Get To Know
          </span>
          <h2
            ref={headingRef}
            className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight"
          >
            About <span className="text-gradient">Me</span>
          </h2>
        </div>

        <div className="grid lg:grid-cols-2 gap-12 lg:gap-20 items-start">
          {/* Content */}
          <div ref={contentRef} className="space-y-6">
            <p className="text-lg text-muted-foreground leading-relaxed">
              I'm a dedicated <span className="text-foreground font-medium">Java Spring Boot Developer</span> and <span className="text-foreground font-medium">Certified SAFe® 6 Professional</span> with{' '}
              <span className="text-foreground font-medium">3+ years of professional experience</span>. I specialize in backend development, microservices architecture, and enterprise automation.
            </p>
            
            <p className="text-lg text-muted-foreground leading-relaxed">
              I have deep expertise in <span className="text-foreground font-medium">Agentic AI and Generative AI</span>, leveraging Python and advanced frameworks to build intelligent, autonomous systems. 
              My technical range extends from high-performance Java backends to state-of-the-art AI agent architectures.
            </p>
            
            <p className="text-lg text-muted-foreground leading-relaxed">
              Beyond technical implementation, I am a <span className="text-foreground font-medium">SAFe® 6 Product Owner/Product Manager (POPM)</span> and <span className="text-foreground font-medium">SAFe® 6 Scrum Master (SSM)</span>. 
              This unique blend of technical expertise and Agile leadership allows me to bridge the gap between business strategy and execution, ensuring high-value delivery through optimized Lean-Agile processes.
            </p>
            
            <p className="text-lg text-muted-foreground leading-relaxed">
              I've successfully delivered{' '}
              <span className="text-foreground font-medium">15+ Java projects</span> and <span className="text-foreground font-medium">30+ Zoho implementations</span>. 
              With a problem-solving mindset strengthened by solving 600+ DSA problems, I focus on creating scalable, reliable systems that drive business growth.
            </p>

            {/* What I Bring */}
            <div className="pt-4">
              <h3 className="text-sm font-semibold uppercase tracking-wider text-muted-foreground mb-4">
                What I Bring
              </h3>
              <div className="grid grid-cols-1 xs:grid-cols-2 gap-3">
                {[
                  'Full-Stack Development Expertise',
                  'Java Backend Specialization',
                  'Zoho Platform Integration Expert',
                  'Custom Enterprise Solutions',
                  'Problem Solving Enthusiast',
                  'Continuous Learner',
                ].map((item) => (
                  <div key={item} className="flex items-center gap-2">
                    <span className="w-1.5 h-1.5 rounded-full bg-[#5B8DF7]" />
                    <span className="text-sm text-muted-foreground">{item}</span>
                  </div>
                ))}
              </div>
            </div>

            {/* Key Expertise */}
            <div className="pt-4">
              <h3 className="text-sm font-semibold uppercase tracking-wider text-muted-foreground mb-4">
                Key Expertise
              </h3>
              <div className="flex flex-wrap gap-2">
                {highlights.map((highlight) => (
                  <span
                    key={highlight}
                    className="px-4 py-2 rounded-full glass text-sm font-medium hover:bg-[#5B8DF7]/20 hover:text-[#5B8DF7] transition-colors cursor-default"
                  >
                    {highlight}
                  </span>
                ))}
              </div>
            </div>
          </div>

          {/* Stats Grid */}
          <div ref={statsRef} className="grid grid-cols-2 sm:grid-cols-3 gap-4">
            {stats.map((stat, index) => (
              <div
                key={stat.label}
                className="stat-item glass rounded-2xl p-5 hover:bg-[#5B8DF7]/10 transition-colors group"
                style={{ animationDelay: `${index * 0.1}s` }}
              >
                <div className="w-10 h-10 rounded-xl bg-[#5B8DF7]/20 flex items-center justify-center mb-3 group-hover:bg-[#5B8DF7] group-hover:text-white transition-colors">
                  <stat.icon className="h-5 w-5 text-[#5B8DF7] group-hover:text-white" />
                </div>
                <div className="text-2xl sm:text-3xl font-bold mb-1">{stat.value}</div>
                <div className="text-xs text-muted-foreground">{stat.label}</div>
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}
