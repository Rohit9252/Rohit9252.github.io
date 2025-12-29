import React, { useEffect, useRef, useState } from 'react'
import "./About.css"
import ME from "../../assets/profile-new.jpeg"
import { FaAward, FaGraduationCap, FaCode, FaLaptopCode, FaUsers, FaCoffee, FaRocket } from "react-icons/fa"
import { GoProject } from "react-icons/go"
import { SiLeetcode } from "react-icons/si"
import { MdWorkOutline } from "react-icons/md"
import { BiTime } from "react-icons/bi"

const About = () => {
  const [isVisible, setIsVisible] = useState(false);
  const aboutRef = useRef(null);

  const stats = [
    { icon: MdWorkOutline, title: "Experience", value: "3+", unit: "Years", color: "#3b82f6" },
    { icon: SiLeetcode, title: "Zoho Implementations", value: "30+", unit: "Delivered", color: "#e11d48" },
    { icon: SiLeetcode, title: "DSA Problems", value: "600+", unit: "Solved", color: "#f59e0b" },
  ];

  const highlights = [
    { icon: FaLaptopCode, text: "Full-Stack Development Expertise" },
    { icon: FaRocket, text: "Java Backend Specialization" },
    { icon: FaCoffee, text: "Zoho Platform Integration Expert" },
    { icon: FaAward, text: "Custom Enterprise Solutions" },
    { icon: FaCoffee, text: "Problem Solving Enthusiast" }
  ];

  useEffect(() => {
    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            setIsVisible(true);
          }
        });
      },
      { threshold: 0.3 }
    );

    if (aboutRef.current) {
      observer.observe(aboutRef.current);
    }

    return () => observer.disconnect();
  }, []);

  return (
    <section id='about' className='about-section' ref={aboutRef}>
      <div className='about-header'>
        <span className='section-subtitle'>Get To Know</span>
        <h1 className='section-title'>About Me</h1>
        <p className='section-intro'>
          Passionate Backend Software Engineer with 3+ years of experience in building scalable web applications
        </p>
      </div>

      <div className="about-container">
        <div className="about-left">
          <div className="about-image-wrapper">
            <div className="about-image-container">
              <img src={ME} alt="Rohit - Full Stack Developer" className='about-image' />
              <div className="image-overlay">
                <div className="experience-badge">
                  <BiTime className="badge-icon" />
                  <span className="badge-text">3+ Years Experience</span>
                </div>
              </div>
            </div>
          </div>
        </div>

        <div className="about-right">
          {/* Statistics Grid */}
          <div className="stats-grid">
            {stats.map((stat, index) => {
              const IconComponent = stat.icon;
              return (
                <div 
                  key={index} 
                  className={`stat-card ${isVisible ? 'animate-in' : ''}`}
                  style={{ '--delay': `${index * 0.1}s`, '--color': stat.color }}
                >
                  <div className="stat-icon-wrapper">
                    <IconComponent className="stat-icon" />
                  </div>
                  <div className="stat-content">
                    <div className="stat-number">{stat.value}</div>
                    <div className="stat-label">{stat.title}</div>
                    <div className="stat-unit">{stat.unit}</div>
                  </div>
                </div>
              );
            })}
          </div>

          {/* About Description */}
          <div className="about-description">
            <h3 className="description-title">My Journey</h3>
            <p className='description-text'>
              I'm a dedicated <strong>Java Spring Boot Developer</strong> with <strong>3+ years of professional experience</strong> specializing in <strong>Java backend development</strong>, <strong>Spring Boot applications</strong>, and <strong>Zoho platform implementations</strong>. My expertise lies in creating scalable, efficient enterprise solutions that solve complex business problems.
            </p>
            <p className='description-text'>
              Throughout my career, I've successfully delivered <strong>15+ Java projects</strong>, completed <strong>30+ Zoho implementations</strong> with <strong>custom development solutions</strong> tailored to client needs and specifications, and collaborated with diverse teams across multiple industries. I specialize in <strong>Java Spring Boot development</strong>, <strong>enterprise automation</strong>, and <strong>custom CRM solutions</strong> that streamline business operations and enhance productivity.
            </p>
          </div>

          {/* Highlights */}
          <div className="about-highlights">
            <h4 className="highlights-title">What I Bring</h4>
            <div className="highlights-grid">
              {highlights.map((highlight, index) => {
                const IconComponent = highlight.icon;
                return (
                  <div key={index} className={`highlight-item ${isVisible ? 'animate-in' : ''}`} style={{ '--delay': `${0.8 + index * 0.1}s` }}>
                    <IconComponent className="highlight-icon" />
                    <span className="highlight-text">{highlight.text}</span>
                  </div>
                );
              })}
            </div>
          </div>

          {/* CTA Button */}
          <div className="about-cta">
            <a href="#contact" className='cta-button'>
              <span>Let's Work Together</span>
              <FaRocket className="cta-icon" />
            </a>
          </div>
        </div>
      </div>
    </section>
  )
}

export default About