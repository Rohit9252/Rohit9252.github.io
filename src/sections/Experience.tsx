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
          gsap.fromTo(
            item,
            { x: index % 2 === 0 ? -50 : 50, opacity: 0 },
            {
              x: 0,
              opacity: 1,
              duration: 0.8,
              ease: 'expo.out',
              scrollTrigger: {
                trigger: item,
                start: 'top 75%',
                toggleActions: 'play none none reverse',
              },
            }
          );
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
        <div ref={timelineRef} className="relative max-w-4xl mx-auto">
          {/* Timeline Line */}
          <div className="absolute left-4 md:left-1/2 top-0 bottom-0 w-0.5 bg-border md:-translate-x-1/2 origin-top timeline-line" />

          {/* Experience Items */}
          <div className="space-y-12">
            {experiences.map((exp, index) => (
              <div
                key={exp.company}
                className={`timeline-item relative flex flex-col md:flex-row gap-8 ${
                  index % 2 === 0 ? 'md:flex-row' : 'md:flex-row-reverse'
                }`}
              >
                {/* Timeline Dot */}
                <div className="absolute left-4 md:left-1/2 w-4 h-4 rounded-full bg-[#5B8DF7] border-4 border-background md:-translate-x-1/2 z-10 glow-blue" />

                {/* Content Card */}
                <div className={`ml-12 md:ml-0 md:w-[calc(50%-2rem)] ${
                  index % 2 === 0 ? 'md:pr-8' : 'md:pl-8'
                }`}>
                  <div className="glass rounded-2xl p-6 sm:p-8 hover:bg-[#5B8DF7]/5 transition-colors group">
                    {/* Header */}
                    <div className="flex flex-wrap items-start justify-between gap-4 mb-4">
                      <div>
                        <h3 className="text-xl font-bold mb-1 group-hover:text-[#5B8DF7] transition-colors">
                          {exp.role}
                        </h3>
                        <div className="flex items-center gap-2 text-muted-foreground">
                          <Building2 className="h-4 w-4" />
                          <span className="font-medium">{exp.company}</span>
                        </div>
                      </div>
                      <span className={`px-3 py-1 rounded-full text-xs font-medium ${
                        exp.type === 'Internship' 
                          ? 'bg-purple-500/20 text-purple-500' 
                          : 'bg-[#5B8DF7]/20 text-[#5B8DF7]'
                      }`}>
                        {exp.type}
                      </span>
                    </div>

                    {/* Meta */}
                    <div className="flex flex-wrap gap-4 text-sm text-muted-foreground mb-4">
                      <div className="flex items-center gap-1.5">
                        <Calendar className="h-4 w-4" />
                        <span>{exp.period}</span>
                      </div>
                      <div className="flex items-center gap-1.5">
                        <MapPin className="h-4 w-4" />
                        <span>{exp.location}</span>
                      </div>
                    </div>

                    {/* Description */}
                    <p className="text-muted-foreground mb-4">{exp.description}</p>

                    {/* Achievements */}
                    <div className="mb-4">
                      <div className="flex items-center gap-2 mb-2">
                        <Trophy className="h-4 w-4 text-[#5B8DF7]" />
                        <span className="text-sm font-semibold">Key Achievements</span>
                      </div>
                      <ul className="space-y-1.5">
                        {exp.achievements.slice(0, 5).map((achievement, i) => (
                          <li key={i} className="flex items-start gap-2 text-sm">
                            <span className="w-1.5 h-1.5 rounded-full bg-[#5B8DF7] mt-1.5 flex-shrink-0" />
                            <span className="text-muted-foreground">{achievement}</span>
                          </li>
                        ))}
                      </ul>
                    </div>

                    {/* Skills */}
                    <div className="flex flex-wrap gap-2">
                      {exp.skills.map((skill) => (
                        <span
                          key={skill}
                          className="px-3 py-1 rounded-full bg-secondary text-xs font-medium"
                        >
                          {skill}
                        </span>
                      ))}
                    </div>
                  </div>
                </div>

                {/* Empty space for alternating layout */}
                <div className="hidden md:block md:w-[calc(50%-2rem)]" />
              </div>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}
