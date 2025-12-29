import React, { useState, useEffect } from "react";
import "./experience.css";
import { 
  FaHtml5, 
  FaCss3Alt, 
  FaJava, 
  FaReact, 
  FaNodeJs, 
  FaGitAlt, 
  FaDocker, 
  FaAws 
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
  SiAwslambda
} from "react-icons/si";

const Experience = () => {
  const [activeCategory, setActiveCategory] = useState(0);
  const [isVisible, setIsVisible] = useState(false);

  useEffect(() => {
    setIsVisible(true);
  }, []);

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

  return (
    <section id="skills" className={`skills-section ${isVisible ? 'visible' : ''}`}>
      <div className="skills-header">
        <h4>What Skills I Have</h4>
        <h1>My Technical Arsenal</h1>
        <div className="skills-subtitle">
          <p>Crafting digital experiences with cutting-edge technologies</p>
        </div>
      </div>

      <div className="skills-container">
        <div className="category-tabs">
          {techCategories.map((category, index) => (
            <button
              key={index}
              className={`category-tab ${activeCategory === index ? 'active' : ''}`}
              onClick={() => setActiveCategory(index)}
              style={{ '--category-color': category.color }}
            >
              <span className="tab-title">{category.title}</span>
              <span className="tab-count">{category.technologies.length}</span>
            </button>
          ))}
        </div>

        <div className="skills-content">
          <div className="category-display">
            <h3 className="category-title" style={{ color: techCategories[activeCategory].color }}>
              {techCategories[activeCategory].title} Development
            </h3>
            
            <div className="skills-grid">
              {techCategories[activeCategory].technologies.map((tech, index) => (
                <div 
                  key={index} 
                  className="skill-card"
                  style={{ 
                    '--delay': `${index * 0.1}s`,
                    '--tech-color': tech.color 
                  }}
                >
                  <div className="skill-icon-wrapper">
                    <div className="skill-icon" style={{ color: tech.color }}>
                      {tech.icon}
                    </div>
                    <div className="skill-glow" style={{ backgroundColor: tech.color }}></div>
                  </div>
                  
                  <div className="skill-info">
                    <h4>{tech.name}</h4>
                    <div className="skill-level">
                      <div className="level-bar">
                        <div 
                          className="level-fill" 
                          style={{ 
                            width: `${tech.level}%`,
                            backgroundColor: tech.color 
                          }}
                        ></div>
                      </div>
                      <span className="level-text">{tech.level}%</span>
                    </div>
                  </div>
                  
                  <div className="skill-particles">
                    <div className="particle"></div>
                    <div className="particle"></div>
                    <div className="particle"></div>
                  </div>
                </div>
              ))}
            </div>
          </div>
        </div>

        <div className="skills-stats">
          <div className="stat-item">
            <span className="stat-number">25+</span>
            <span className="stat-label">Technologies</span>
          </div>
          <div className="stat-item">
            <span className="stat-number">3+</span>
            <span className="stat-label">Years Experience</span>
          </div>
          <div className="stat-item">
            <span className="stat-number">50+</span>
            <span className="stat-label">Projects Built</span>
          </div>
        </div>
      </div>
    </section>
  );
};

export default Experience;