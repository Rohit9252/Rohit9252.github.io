import { useEffect, useRef, useState } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { 
  FaHtml5, 
  FaCss3Alt, 
  FaJava, 
  FaReact, 
  FaNodeJs, 
  FaGitAlt, 
  FaDocker, 
  FaAws,
  FaUsers,
  FaUsersCog,
  FaProjectDiagram,
  FaChartLine,
  FaLightbulb,
  FaTasks,
  FaGem
} from "react-icons/fa";
import { 
  DiJavascript1, 
  DiMongodb 
} from "react-icons/di";
import {
  SiMysql,
  SiExpress,
  SiTailwindcss,
  SiSpringboot,
  SiHibernate,
  SiPostgresql,
  SiRedis,
  SiKubernetes,
  SiJenkins,
  SiAwslambda,
  SiLeanpub
} from "react-icons/si";

gsap.registerPlugin(ScrollTrigger);

const techCategories = [
  {
    title: "Frontend",
    color: "#e74c3c",
    technologies: [
      { name: "HTML5", icon: <FaHtml5 />, level: 95, color: "#e34c26" },
      { name: "CSS3", icon: <FaCss3Alt />, level: 90, color: "#1572b6" },
      { name: "JavaScript", icon: <DiJavascript1 />, level: 88, color: "#f7df1e" },
      { name: "React", icon: <FaReact />, level: 85, color: "#61dafb" },
      { name: "Tailwind", icon: <SiTailwindcss />, level: 80, color: "#06b6d4" }
    ]
  },
  {
    title: "Backend",
    color: "#3498db",
    technologies: [
      { name: "Java", icon: <FaJava />, level: 95, color: "#ed8b00" },
      { name: "Spring Boot", icon: <SiSpringboot />, level: 90, color: "#6db33f" },
      { name: "Node.js", icon: <FaNodeJs />, level: 85, color: "#339933" },
      { name: "Express.js", icon: <SiExpress />, level: 80, color: "#000000" },
      { name: "Hibernate", icon: <SiHibernate />, level: 75, color: "#59666c" }
    ]
  },
  {
    title: "Agile & SAFe®",
    color: "#00a3e0",
    technologies: [
      { name: "Scaled Agile Framework®", icon: <FaUsers />, level: 95, color: "#00a3e0" },
      { name: "Product Ownership", icon: <FaProjectDiagram />, level: 90, color: "#00a3e0" },
      { name: "Agile Methodologies", icon: <FaUsersCog />, level: 95, color: "#00a3e0" },
      { name: "Backlog Refinement", icon: <FaTasks />, level: 92, color: "#00a3e0" },
      { name: "Lean-Agile", icon: <SiLeanpub />, level: 88, color: "#00a3e0" },
      { name: "Value Definition", icon: <FaGem />, level: 85, color: "#00a3e0" },
      { name: "Business Case Development", icon: <FaChartLine />, level: 82, color: "#00a3e0" },
      { name: "Product Management", icon: <FaLightbulb />, level: 85, color: "#00a3e0" },
      { name: "SAFe® Principles", icon: <FaUsers />, level: 90, color: "#00a3e0" }
    ]
  },
  {
    title: "Databases",
    color: "#9b59b6",
    technologies: [
      { name: "MySQL", icon: <SiMysql />, level: 90, color: "#4479a1" },
      { name: "PostgreSQL", icon: <SiPostgresql />, level: 85, color: "#336791" },
      { name: "MongoDB", icon: <DiMongodb />, level: 80, color: "#47a248" },
      { name: "Redis", icon: <SiRedis />, level: 70, color: "#dc382d" }
    ]
  },
  {
    title: "Cloud & AWS",
    color: "#f39c12",
    technologies: [
      { name: "AWS Lambda", icon: <SiAwslambda />, level: 85, color: "#ff9900" },
      { name: "AWS EC2", icon: <FaAws />, level: 80, color: "#ff9900" },
      { name: "AWS S3", icon: <FaAws />, level: 85, color: "#ff9900" },
      { name: "AWS SQS", icon: <FaAws />, level: 75, color: "#ff9900" }
    ]
  },
  {
    title: "DevOps",
    color: "#2ecc71",
    technologies: [
      { name: "Docker", icon: <FaDocker />, level: 80, color: "#2496ed" },
      { name: "Git", icon: <FaGitAlt />, level: 95, color: "#f05032" },
      { name: "Kubernetes", icon: <SiKubernetes />, level: 70, color: "#326ce5" },
      { name: "Jenkins", icon: <SiJenkins />, level: 65, color: "#d33833" }
    ]
  }
];

export default function Skills() {
  const sectionRef = useRef<HTMLElement>(null);
  const headingRef = useRef<HTMLDivElement>(null);
  const tabsRef = useRef<HTMLDivElement>(null);
  const contentRef = useRef<HTMLDivElement>(null);
  const [activeCategory, setActiveCategory] = useState(0);

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

      // Tabs animation
      gsap.fromTo(
        tabsRef.current?.children || [],
        { y: 30, opacity: 0 },
        {
          y: 0,
          opacity: 1,
          duration: 0.6,
          stagger: 0.1,
          ease: 'expo.out',
          scrollTrigger: {
            trigger: tabsRef.current,
            start: 'top 85%',
          }
        }
      );
    }, sectionRef);

    return () => ctx.revert();
  }, []);

  // Animation for content when category changes
  useEffect(() => {
    if (contentRef.current) {
      gsap.fromTo(
        contentRef.current.querySelectorAll('.skill-card'),
        { y: 20, opacity: 0, scale: 0.95 },
        {
          y: 0,
          opacity: 1,
          scale: 1,
          duration: 0.5,
          stagger: 0.05,
          ease: 'back.out(1.7)',
        }
      );
    }
  }, [activeCategory]);

  return (
    <section
      ref={sectionRef}
      id="skills"
      className="relative py-24 sm:py-32 overflow-hidden bg-background text-foreground"
    >
      {/* Background Blobs */}
      <div className="absolute inset-0 pointer-events-none">
        <div 
          className="absolute top-0 left-1/4 w-96 h-96 rounded-full blur-[120px] opacity-20 dark:opacity-10" 
          style={{ backgroundColor: techCategories[activeCategory].color }}
        />
        <div className="absolute bottom-0 right-1/4 w-80 h-80 bg-purple-500/10 rounded-full blur-[100px] opacity-20 dark:opacity-10" />
      </div>

      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        {/* Section Header */}
        <div ref={headingRef} className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-primary mb-4 border border-primary/20">
            Technical Arsenal
          </span>
          <h2 className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight mb-4">
            My <span className="text-gradient">Technical Arsenal</span>
          </h2>
          <p className="text-lg text-muted-foreground max-w-2xl mx-auto italic">
            Crafting digital experiences with cutting-edge technologies.
          </p>
        </div>

        {/* Category Tabs */}
        <div 
          ref={tabsRef}
          className="flex flex-wrap justify-center gap-3 sm:gap-4 mb-12"
        >
          {techCategories.map((category, index) => (
            <button
              key={category.title}
              onClick={() => setActiveCategory(index)}
              className={`group relative flex items-center gap-3 px-6 py-3 rounded-full text-sm font-semibold transition-all duration-500 ${
                activeCategory === index
                  ? 'text-white shadow-lg'
                  : 'glass text-muted-foreground hover:text-foreground'
              }`}
              style={{ 
                backgroundColor: activeCategory === index ? category.color : undefined,
                borderColor: activeCategory === index ? category.color : undefined
              }}
            >
              <span className="relative z-10">{category.title}</span>
              <span className={`flex items-center justify-center w-6 h-6 rounded-full text-[10px] font-bold transition-colors ${
                activeCategory === index ? 'bg-white/20 text-white' : 'bg-muted text-muted-foreground'
              }`}>
                {category.technologies.length}
              </span>
              {activeCategory === index && (
                <div 
                  className="absolute inset-0 rounded-full blur-md opacity-50 -z-10"
                  style={{ backgroundColor: category.color }}
                />
              )}
            </button>
          ))}
        </div>

        {/* Skills Display */}
        <div ref={contentRef} className="max-w-6xl mx-auto">
          <div className="text-center mb-10">
            <h3 
              className="text-2xl sm:text-3xl font-bold transition-colors duration-500"
              style={{ color: techCategories[activeCategory].color }}
            >
              {techCategories[activeCategory].title} Development
            </h3>
            <div 
              className="w-20 h-1 mx-auto mt-2 rounded-full transition-all duration-500"
              style={{ backgroundColor: techCategories[activeCategory].color }}
            />
          </div>

          <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-6">
            {techCategories[activeCategory].technologies.map((tech) => (
              <div
                key={tech.name}
                className="group relative glass p-6 rounded-2xl border hover:border-transparent transition-all duration-500 hover:-translate-y-2 overflow-hidden"
              >
                {/* Hover Border Effect */}
                <div 
                  className="absolute inset-x-0 top-0 h-[2px] scale-x-0 group-hover:scale-x-100 transition-transform duration-500 origin-left"
                  style={{ backgroundColor: tech.color }}
                />

                {/* Skill Icon */}
                <div className="relative mb-6 flex justify-center">
                  <div 
                    className="text-5xl sm:text-6xl transition-all duration-500 group-hover:scale-110 group-hover:rotate-6 z-10"
                    style={{ color: tech.color }}
                  >
                    {tech.icon}
                  </div>
                  <div 
                    className="absolute inset-0 blur-2xl opacity-0 group-hover:opacity-20 transition-opacity duration-500 rounded-full"
                    style={{ backgroundColor: tech.color }}
                  />
                </div>

                {/* Skill Info */}
                <div className="text-center">
                  <h4 className="text-lg font-bold mb-4">{tech.name}</h4>
                  
                  <div className="flex items-center gap-4">
                    <div className="flex-1 h-2 rounded-full bg-secondary/50 overflow-hidden relative">
                      <div
                        className="h-full rounded-full transition-all duration-1000 ease-out relative overflow-hidden"
                        style={{ 
                          width: `${tech.level}%`,
                          backgroundColor: tech.color 
                        }}
                      >
                        {/* Shimmer Effect */}
                        <div className="absolute inset-0 bg-gradient-to-r from-transparent via-white/30 to-transparent -translate-x-full animate-[shimmer_2s_infinite]" />
                      </div>
                    </div>
                    <span 
                      className="text-sm font-bold min-w-[35px]"
                      style={{ color: tech.color }}
                    >
                      {tech.level}%
                    </span>
                  </div>
                </div>

                {/* Decorative Particles (simplified) */}
                <div className="absolute inset-0 pointer-events-none opacity-0 group-hover:opacity-100 transition-opacity duration-500">
                  {[...Array(3)].map((_, i) => (
                    <div 
                      key={i}
                      className="absolute w-1 h-1 rounded-full animate-float"
                      style={{ 
                        backgroundColor: tech.color,
                        top: `${20 + i * 30}%`,
                        left: `${15 + i * 40}%`,
                        animationDelay: `${i * 0.5}s`,
                        animationDuration: `${2 + i}s`
                      }}
                    />
                  ))}
                </div>
              </div>
            ))}
          </div>
        </div>

      </div>

      <style>{`
        @keyframes shimmer {
          0% { transform: translateX(-100%); }
          100% { transform: translateX(100%); }
        }
      `}</style>
    </section>
  );
}
