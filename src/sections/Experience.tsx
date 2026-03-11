import { useEffect, useRef } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { Building2, Calendar, MapPin, Trophy } from 'lucide-react';

gsap.registerPlugin(ScrollTrigger);

const experiences = [
  {
    company: 'Noduco Software Private Limited',
    role: 'Software Engineer (Backend)',
    period: 'July 2024 - Present',
    location: 'Remote',
    type: 'Full-time',
    description: 'Core backend developer on Builder\'s Edge platform, owning end-to-end backend architecture from system design to production deployment.',
    achievements: [
      'Designed and built scalable backend microservices using Java, Spring Boot, and Spring Cloud',
      'Architected MLS-compliant data ingestion pipelines with license-aware access controls',
      'Implemented event-driven architecture using Apache Kafka, Amazon SQS, and Amazon SNS',
      'Reduced API response latency by ~35% through Redis (AWS ElastiCache) caching',
      'Lowered database load by ~20% with optimized read patterns',
      'Built and maintained RESTful APIs for real estate listings and analytics',
      'Owned cloud infrastructure on AWS (EC2, S3, IAM, CloudWatch) with Docker containerization',
      'Implemented CI/CD pipelines via GitHub Actions for automated deployments',
      'Wrote unit and integration tests using JUnit and Mockito ensuring high test coverage',
    ],
    skills: ['Java', 'Spring Boot', 'Spring Cloud', 'Apache Kafka', 'Amazon SQS', 'Amazon SNS', 'Redis', 'AWS', 'Docker', 'JUnit', 'Mockito', 'MLS APIs'],
  },
  {
    company: 'CBOS IT Pvt. Ltd.',
    role: 'Software Developer / Consultant (Backend)',
    period: 'April 2023 - July 2024',
    location: 'Remote',
    type: 'Full-time',
    description: 'Designed and developed enterprise solutions for construction industry SaaS platform and financial systems.',
    achievements: [
      'Designed and developed location-aware project discovery system using Java and Spring Boot',
      'Integrated Zoho CRM APIs to fetch and filter projects based on geographical area',
      'Built backend integrations with Barbara, Glenigan, and CIS APIs',
      'Implemented enterprise CRM integrations across Zoho ecosystem',
      'Processed 100K+ records for 10-12 enterprise clients',
      'Implemented AIB-compliant transaction XML files for EU and UK banking systems',
      'Delivered 30+ Zoho implementations with custom development solutions',
    ],
    skills: ['Java', 'Spring Boot', 'Zoho CRM', 'MySQL', 'REST APIs', 'Financial Systems', 'AIB Compliance'],
  },
  {
    company: 'Mad Brains',
    role: 'Software Developer Intern',
    period: 'January 2023 - March 2023',
    location: 'Remote',
    type: 'Internship',
    description: 'Gained hands-on experience in full-stack development working on real-world projects.',
    achievements: [
      'Developed and maintained web applications using modern technologies',
      'Collaborated with senior developers on feature implementation',
      'Learned industry best practices for code quality and testing',
      'Participated in agile development processes',
    ],
    skills: ['Java', 'Spring Boot', 'React', 'MySQL', 'Git'],
  },
];

export default function Experience() {
  const sectionRef = useRef<HTMLElement>(null);
  const headingRef = useRef<HTMLDivElement>(null);
  const timelineRef = useRef<HTMLDivElement>(null);

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

      // Timeline items animation
      const items = timelineRef.current?.querySelectorAll('.timeline-item');
      if (items) {
        items.forEach((item, index) => {
          const card = item.querySelector('.timeline-card');
          const period = item.querySelector('.timeline-period');

          if (card) {
            gsap.fromTo(
              card,
              { x: index % 2 === 0 ? -100 : 100, opacity: 0 },
              {
                x: 0,
                opacity: 1,
                duration: 1,
                ease: 'expo.out',
                scrollTrigger: {
                  trigger: card,
                  start: 'top 85%',
                  toggleActions: 'play none none reverse',
                },
              }
            );
          }

          if (period) {
            gsap.fromTo(
              period,
              { x: index % 2 === 0 ? 100 : -100, opacity: 0 },
              {
                x: 0,
                opacity: 1,
                duration: 1,
                ease: 'expo.out',
                scrollTrigger: {
                  trigger: period,
                  start: 'top 85%',
                  toggleActions: 'play none none reverse',
                },
              }
            );
          }
        });
      }

      // Timeline line animation
      const line = timelineRef.current?.querySelector('.timeline-line');
      if (line) {
        gsap.fromTo(
          line,
          { scaleY: 0 },
          {
            scaleY: 1,
            duration: 1.5,
            ease: 'expo.out',
            scrollTrigger: {
              trigger: timelineRef.current,
              start: 'top 70%',
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
      id="experience"
      className="relative py-24 sm:py-32 overflow-hidden"
    >
      {/* Background */}
      <div className="absolute inset-0 pointer-events-none">
        <div className="absolute top-1/2 left-0 w-full h-1/2 bg-gradient-to-t from-[#5B8DF7]/5 to-transparent" />
      </div>

      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        {/* Section Header */}
        <div ref={headingRef} className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-[#5B8DF7] mb-4">
            Work Experience
          </span>
          <h2 className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight mb-4">
            My Professional <span className="text-gradient">Journey</span>
          </h2>
          <p className="text-lg text-muted-foreground max-w-2xl mx-auto">
            A track record of delivering scalable backend solutions across real estate and fintech domains.
          </p>
        </div>

        {/* Timeline */}
        <div ref={timelineRef} className="relative max-w-6xl mx-auto">
          {/* Timeline Line */}
          <div className="absolute left-4 md:left-1/2 top-0 bottom-0 w-0.5 bg-border md:-translate-x-1/2 origin-top timeline-line" />

          {/* Experience Items */}
          <div className="space-y-16">
            {experiences.map((exp, index) => (
              <div
                key={exp.company}
                className={`timeline-item relative flex flex-col ${
                  index % 2 === 0 ? 'md:flex-row' : 'md:flex-row-reverse'
                } items-start`}
              >
                {/* Timeline Dot */}
                <div className="absolute left-4 md:left-1/2 w-5 h-5 rounded-full bg-background border-4 border-[#5B8DF7] md:-translate-x-1/2 z-10 glow-blue mt-8 md:mt-10" />

                {/* Content Card */}
                <div className={`timeline-card ml-12 md:ml-0 md:w-1/2 ${
                  index % 2 === 0 ? 'md:pr-16' : 'md:pl-16'
                }`}>
                  <div className="glass rounded-2xl p-6 sm:p-8 hover:bg-[#5B8DF7]/[0.02] transition-all duration-500 group border border-white/10 hover:border-[#5B8DF7]/30 shadow-2xl shadow-black/20">
                    {/* Header */}
                    <div className="flex flex-wrap items-start justify-between gap-4 mb-6">
                      <div className="flex-1">
                        <h3 className="text-2xl sm:text-3xl font-bold mb-2 group-hover:text-[#5B8DF7] transition-colors leading-tight">
                          {exp.role}
                        </h3>
                        <div className="flex items-center gap-2 text-[#5B8DF7] font-bold text-lg">
                          <Building2 className="h-5 w-5" />
                          <span>{exp.company}</span>
                        </div>
                      </div>
                      <span className={`px-4 py-1.5 rounded-full text-xs font-bold uppercase tracking-wider self-start ${
                        exp.type === 'Internship' 
                          ? 'bg-purple-500/10 text-purple-400 border border-purple-500/20' 
                          : 'bg-[#5B8DF7]/10 text-[#5B8DF7] border border-[#5B8DF7]/20'
                      }`}>
                        {exp.type}
                      </span>
                    </div>

                    {/* Meta - Mobile Only */}
                    <div className="md:hidden flex flex-wrap gap-4 text-sm text-muted-foreground mb-6 pb-6 border-b border-white/5">
                      <div className="flex items-center gap-1.5 bg-white/5 px-3 py-1 rounded-lg border border-white/5">
                        <Calendar className="h-3.5 w-3.5 text-[#5B8DF7]" />
                        <span>{exp.period}</span>
                      </div>
                      <div className="flex items-center gap-1.5 bg-white/5 px-3 py-1 rounded-lg border border-white/5">
                        <MapPin className="h-3.5 w-3.5 text-[#5B8DF7]" />
                        <span>{exp.location}</span>
                      </div>
                    </div>

                    {/* Description */}
                    <div className="relative mb-8">
                      <div className="absolute -left-4 top-0 bottom-0 w-1 bg-[#5B8DF7]/20 rounded-full" />
                      <p className="text-muted-foreground leading-relaxed pl-4 italic">
                        "{exp.description}"
                      </p>
                    </div>

                    {/* Achievements */}
                    <div className="mb-8">
                      <div className="flex items-center gap-2 mb-6">
                        <div className="p-1.5 rounded-lg bg-[#5B8DF7]/10">
                          <Trophy className="h-4 w-4 text-[#5B8DF7]" />
                        </div>
                        <span className="text-sm font-bold uppercase tracking-widest text-foreground/80">Key Contributions</span>
                      </div>
                      <ul className="space-y-4">
                        {exp.achievements.map((achievement, i) => (
                          <li key={i} className="flex items-start gap-4 text-sm group/item">
                            <span className="w-2 h-2 rounded-full bg-[#5B8DF7] mt-1.5 flex-shrink-0 shadow-[0_0_8px_rgba(91,141,247,0.8)] group-hover/item:scale-125 transition-transform" />
                            <span className="text-muted-foreground leading-relaxed group-hover/item:text-foreground transition-colors">{achievement}</span>
                          </li>
                        ))}
                      </ul>
                    </div>

                    {/* Skills */}
                    <div className="pt-6 border-t border-white/5">
                      <div className="flex flex-wrap gap-2">
                        {exp.skills.map((skill) => (
                          <span
                            key={skill}
                            className="px-3 py-1.5 rounded-lg bg-white/5 text-xs font-medium text-muted-foreground hover:text-[#5B8DF7] hover:bg-[#5B8DF7]/10 hover:border-[#5B8DF7]/20 transition-all duration-300 border border-white/5"
                          >
                            {skill}
                          </span>
                        ))}
                      </div>
                    </div>
                  </div>
                </div>

                {/* Period & Location - Desktop Only */}
                <div className={`timeline-period hidden md:flex md:w-1/2 mt-10 ${
                  index % 2 === 0 ? 'md:pl-16 justify-start' : 'md:pr-16 justify-end text-right'
                }`}>
                  <div className="flex flex-col gap-4">
                    <div className={`flex items-center gap-3 ${index % 2 === 0 ? 'flex-row' : 'flex-row-reverse'}`}>
                      <div className="p-3 rounded-2xl glass border-white/10 text-[#5B8DF7] shadow-lg">
                        <Calendar className="h-6 w-6" />
                      </div>
                      <span className="text-2xl font-bold tracking-tight text-foreground/90">{exp.period}</span>
                    </div>
                    <div className={`flex items-center gap-3 text-muted-foreground ${index % 2 === 0 ? 'flex-row' : 'flex-row-reverse'}`}>
                      <MapPin className="h-5 w-5 text-[#5B8DF7]" />
                      <span className="text-lg font-medium">{exp.location}</span>
                    </div>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}
