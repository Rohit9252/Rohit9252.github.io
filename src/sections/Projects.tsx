import { useEffect, useRef } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { ExternalLink, Github, Database, GraduationCap, ShoppingBag, Sprout, Youtube, TrendingUp } from 'lucide-react';
import { Button } from '@/components/ui/button';
import useEmblaCarousel from 'embla-carousel-react';
import Autoplay from 'embla-carousel-autoplay';

gsap.registerPlugin(ScrollTrigger);

const projects = [
  {
    title: 'MLS Data Pipeline',
    description: 'A comprehensive MLS (Multiple Listing Service) data ingestion and processing system that handles 50K-100K property listings with real-time validation, normalization, and license-aware access controls.',
    icon: Database,
    tags: ['Java', 'Spring Boot', 'MongoDB', 'Kafka', 'Redis', 'AWS'],
    highlights: [
      'Processes 50K-100K property listings daily',
      'Reduced API latency by ~35% with Redis caching',
      'Kafka-based async processing for non-blocking jobs',
      'MLS compliance and licensing logic',
    ],
    color: 'from-blue-500 to-cyan-500',
    github: 'https://github.com/rohit9252',
    demo: '#',
    type: 'Professional',
  },
  {
    title: 'E-Commerce API',
    description: 'A comprehensive REST API for an e-commerce platform where customers can browse products, manage their shopping cart, and place orders for Men, Women & Kids clothing.',
    icon: ShoppingBag,
    tags: ['Java', 'Spring Boot', 'MySQL', 'REST APIs', 'Hibernate'],
    highlights: [
      'Complete e-commerce functionality',
      'Product catalog with categories',
      'Shopping cart management',
      'Order processing system',
    ],
    color: 'from-green-500 to-emerald-500',
    github: 'https://github.com/Dev-Mriganka/REST-API-Ecommerce-Site',
    demo: 'http://170.187.233.233:8888/user/items',
    type: 'Group Project',
  },
  {
    title: 'Exam Portal',
    description: 'A modern examination portal built with Java SpringBoot and Angular featuring user registration, login system, exam creation, and result management with PostgreSQL database.',
    icon: GraduationCap,
    tags: ['Java', 'Spring Boot', 'PostgreSQL', 'Angular', 'TypeScript'],
    highlights: [
      'User authentication and authorization',
      'Exam creation and management',
      'Real-time result calculation',
      'Responsive Angular frontend',
    ],
    color: 'from-purple-500 to-pink-500',
    github: 'https://github.com/Rohit9252/Edcater-Exam-Portal',
    demo: 'https://exam-portal-github-io.vercel.app/',
    type: 'Group Project',
  },
  {
    title: 'Nike Store Clone',
    description: 'A pixel-perfect Nike shoe store clone built with React, providing customers with a seamless shopping experience featuring product browsing, cart management, and responsive design.',
    icon: ShoppingBag,
    tags: ['React', 'Tailwind CSS', 'Node.js', 'Express.js', 'Redux', 'PostgreSQL'],
    highlights: [
      'Pixel-perfect UI replication',
      'Product browsing and filtering',
      'Cart management with Redux',
      'Responsive design',
    ],
    color: 'from-orange-500 to-red-500',
    github: 'https://github.com/Rohit9252/Nike-clone',
    demo: 'https://nike-clone-three.vercel.app/',
    type: 'Solo Project',
  },
  {
    title: 'Plant Nursery API',
    description: 'A collaborative REST API project for an online plant nursery store where customers can browse plants, add them to cart, and place orders. Built by a team of 5 developers.',
    icon: Sprout,
    tags: ['Java', 'Spring Boot', 'MySQL', 'REST APIs', 'Hibernate'],
    highlights: [
      'Plant catalog with categories',
      'Shopping cart functionality',
      'Order placement system',
      'Team collaboration project',
    ],
    color: 'from-green-600 to-teal-500',
    github: 'https://github.com/manojgajare123/peppy-move-2031',
    demo: 'https://drive.google.com/file/d/1UY64WccuAuusjHfYTDw1YyqoCCIOswMv/view',
    type: 'Group Project',
  },
  {
    title: 'YouTube Clone',
    description: 'A feature-rich YouTube clone application that replicates core YouTube functionalities including video browsing, search functionality, and discovery features using Rapid API integration.',
    icon: Youtube,
    tags: ['React', 'JavaScript', 'Rapid API', 'Tailwind CSS'],
    highlights: [
      'Video browsing and search',
      'Rapid API integration',
      'Responsive design',
      'Video discovery features',
    ],
    color: 'from-red-500 to-rose-500',
    github: 'https://github.com/Rohit9252',
    demo: '#',
    type: 'Solo Project',
  },
  {
    title: 'Crypto Tracker',
    description: 'A real-time cryptocurrency tracking application that allows users to monitor latest prices, market information, and trends for popular cryptocurrencies with interactive charts.',
    icon: TrendingUp,
    tags: ['React', 'JavaScript', 'HTML', 'CSS', 'Chart.js'],
    highlights: [
      'Real-time price tracking',
      'Interactive charts',
      'Market trend analysis',
      'Multiple cryptocurrency support',
    ],
    color: 'from-yellow-500 to-amber-500',
    github: 'https://github.com/Rohit9252',
    demo: '#',
    type: 'Solo Project',
  },
];

export default function Projects() {
  const sectionRef = useRef<HTMLElement>(null);
  const headingRef = useRef<HTMLDivElement>(null);
  const gridRef = useRef<HTMLDivElement>(null);
  const [emblaRef] = useEmblaCarousel({ loop: true, align: 'start' }, [
    Autoplay({ delay: 5000, stopOnInteraction: false })
  ]);

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

      // Project cards animation for desktop
      const cards = gridRef.current?.querySelectorAll('.project-card');
      if (cards && cards.length > 0) {
        gsap.fromTo(
          cards,
          { y: 60, opacity: 0, scale: 0.95 },
          {
            y: 0,
            opacity: 1,
            scale: 1,
            duration: 0.8,
            stagger: 0.1,
            ease: 'expo.out',
            scrollTrigger: {
              trigger: gridRef.current,
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
      id="projects"
      className="relative py-24 sm:py-32 overflow-hidden"
    >
      {/* Background */}
      <div className="absolute inset-0 pointer-events-none">
        <div className="absolute top-1/3 right-0 w-1/3 h-1/2 bg-gradient-to-l from-[#5B8DF7]/5 to-transparent" />
        <div className="absolute bottom-0 left-0 w-96 h-96 bg-purple-500/5 rounded-full blur-3xl" />
      </div>

      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        {/* Section Header */}
        <div ref={headingRef} className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-[#5B8DF7] mb-4">
            Featured Projects
          </span>
          <h2 className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight mb-4">
            My Recent <span className="text-gradient">Work</span>
          </h2>
          <p className="text-lg text-muted-foreground max-w-2xl mx-auto">
            Here are some of my favorite projects I've worked on, showcasing my skills in modern web development.
          </p>
        </div>

        {/* Carousel for Mobile, Grid for Desktop */}
        <div className="max-w-7xl mx-auto">
          {/* Mobile Carousel View */}
          <div className="block md:hidden">
            <div className="overflow-hidden" ref={emblaRef}>
              <div className="flex">
                {projects.map((project) => (
                  <div key={project.title} className="flex-[0_0_100%] min-w-0 px-4">
                    <ProjectCard project={project} />
                  </div>
                ))}
              </div>
            </div>
          </div>

          {/* Desktop Grid View */}
          <div ref={gridRef} className="hidden md:grid md:grid-cols-2 lg:grid-cols-3 gap-6">
            {projects.map((project) => (
              <ProjectCard key={project.title} project={project} />
            ))}
          </div>
        </div>
      </div>
    </section>
  );
}

function ProjectCard({ project }: { project: typeof projects[0] }) {
  return (
    <div className="project-card group glass rounded-2xl overflow-hidden hover:bg-[#5B8DF7]/5 transition-all duration-500 flex flex-col h-full">
      {/* Card Header with Gradient */}
      <div className={`h-1.5 bg-gradient-to-r ${project.color}`} />
      
      <div className="p-5 sm:p-6 flex flex-col flex-grow">
        {/* Icon & Title */}
        <div className="flex items-start justify-between mb-3">
          <div className="flex items-center gap-3">
            <div className={`w-10 h-10 rounded-xl bg-gradient-to-br ${project.color} flex items-center justify-center text-white`}>
              <project.icon className="h-5 w-5" />
            </div>
            <div>
              <h3 className="text-lg font-bold group-hover:text-[#5B8DF7] transition-colors line-clamp-1">
                {project.title}
              </h3>
              <span className={`text-xs px-2 py-0.5 rounded-full ${
                project.type === 'Professional' 
                  ? 'bg-[#5B8DF7]/20 text-[#5B8DF7]' 
                  : project.type === 'Solo Project'
                  ? 'bg-green-500/20 text-green-500'
                  : 'bg-purple-500/20 text-purple-500'
              }`}>
                {project.type}
              </span>
            </div>
          </div>
        </div>

        {/* Description */}
        <p className="text-sm text-muted-foreground mb-4 line-clamp-3 flex-grow">
          {project.description}
        </p>

        {/* Highlights */}
        <ul className="space-y-1 mb-4">
          {project.highlights.slice(0, 3).map((highlight, i) => (
            <li key={i} className="flex items-start gap-2 text-xs">
              <span className="w-1 h-1 rounded-full bg-[#5B8DF7] mt-1.5 flex-shrink-0" />
              <span className="text-muted-foreground line-clamp-1">{highlight}</span>
            </li>
          ))}
        </ul>

        {/* Tags */}
        <div className="flex flex-wrap gap-1.5 mb-4">
          {project.tags.slice(0, 4).map((tag) => (
            <span
              key={tag}
              className="px-2 py-0.5 rounded-full bg-secondary text-xs font-medium"
            >
              {tag}
            </span>
          ))}
        </div>

        {/* Actions */}
        <div className="flex gap-2 mt-auto">
          <Button
            variant="outline"
            size="sm"
            className="rounded-lg flex-1 text-xs h-9"
            asChild
          >
            <a href={project.github} target="_blank" rel="noopener noreferrer">
              <Github className="h-3.5 w-3.5 mr-1.5" />
              Code
            </a>
          </Button>
          <Button
            size="sm"
            className={`rounded-lg flex-1 text-xs h-9 bg-gradient-to-r ${project.color} text-white border-0`}
            asChild
          >
            <a href={project.demo} target="_blank" rel="noopener noreferrer">
              <ExternalLink className="h-3.5 w-3.5 mr-1.5" />
              Live Demo
            </a>
          </Button>
        </div>
      </div>
    </div>
  );
}

