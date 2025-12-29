import React, { useEffect, useRef, useState } from 'react'
import "./education.css"
import { FaGraduationCap, FaUniversity, FaSchool, FaCode, FaCalendarAlt, FaMapMarkerAlt, FaAward, FaCertificate } from "react-icons/fa"
import { MdSchool } from "react-icons/md"
import { BiTimeFive } from "react-icons/bi"

const Education = () => {
    const [visibleItems, setVisibleItems] = useState([]);
    const educationRef = useRef(null);

    const educationData = [
        {
            id: 1,
            degree: "Full Stack Web Development",
            institution: "Masai School",
            location: "Bangalore, India",
            duration: "April 2022 - December 2022",
            type: "Intensive Bootcamp",
            description: "Comprehensive full-stack development program focusing on modern web technologies, data structures, algorithms, and system design.",
            skills: ["JavaScript", "React", "Node.js", "MongoDB", "Java", "Spring Boot"],
            icon: FaCode,
            website: "https://www.masaischool.com/",
            color: "#3b82f6",
            grade: "Completed with Excellence"
        },
        {
            id: 2,
            degree: "Bachelor of Arts",
            institution: "Punjab University",
            location: "Chandigarh, India",
            duration: "July 2017 - September 2020",
            type: "Undergraduate Degree",
            description: "Comprehensive liberal arts education with focus on critical thinking, communication skills, and analytical abilities.",
            skills: ["Critical Thinking", "Research", "Communication", "Analysis", "Writing"],
            icon: FaUniversity,
            website: "https://puchd.ac.in/",
            color: "#10b981",
            grade: "First Division"
        },
        {
            id: 3,
            degree: "Higher Secondary (Commerce)",
            institution: "Punjab School Education Board",
            location: "Punjab, India",
            duration: "April 2014 - March 2015",
            type: "Secondary Education",
            description: "Commerce stream education with specialization in business studies, economics, and accountancy.",
            skills: ["Business Studies", "Economics", "Accountancy", "Mathematics", "English"],
            icon: FaSchool,
            website: "https://www.pseb.ac.in/",
            color: "#f59e0b",
            grade: "First Division"
        }
    ];

    useEffect(() => {
        const observer = new IntersectionObserver(
            (entries) => {
                entries.forEach((entry) => {
                    if (entry.isIntersecting) {
                        const id = entry.target.getAttribute('data-id');
                        setVisibleItems(prev => [...new Set([...prev, parseInt(id)])]);
                    }
                });
            },
            { threshold: 0.3, rootMargin: '0px 0px -100px 0px' }
        );

        const educationItems = document.querySelectorAll('.education-item');
        educationItems.forEach(item => observer.observe(item));

        return () => observer.disconnect();
    }, []);

    return (
        <section id="education" className="education-section" ref={educationRef}>
            <div className="education-header">
                <div className="header-icon">
                    <FaGraduationCap className="graduation-icon" />
                </div>
                <span className="section-subtitle">My Academic Journey</span>
                <h1 className="section-title">Education & Qualifications</h1>
                <p className="section-description">
                    My educational journey has been focused on building a strong foundation in technology and continuous learning.
                </p>
            </div>

            <div className="education-timeline">
                <div className="timeline-line"></div>
                
                {educationData.map((education, index) => {
                    const IconComponent = education.icon;
                    const isVisible = visibleItems.includes(education.id);
                    
                    return (
                        <div 
                            key={education.id}
                            className={`education-item ${isVisible ? 'animate-in' : ''} ${index % 2 === 0 ? 'left' : 'right'}`}
                            data-id={education.id}
                        >
                            <div className="timeline-marker" style={{'--marker-color': education.color}}>
                                <IconComponent className="timeline-icon" />
                            </div>
                            
                            <div className="education-card">
                                <div className="card-header">
                                    <div className="degree-info">
                                        <h3 className="degree-title">{education.degree}</h3>
                                        <span className="education-type">{education.type}</span>
                                    </div>
                                    <div className="institution-badge" style={{'--badge-color': education.color}}>
                                        <FaCertificate className="badge-icon" />
                                    </div>
                                </div>
                                
                                <div className="institution-info">
                                    <a href={education.website} target="_blank" rel="noopener noreferrer" className="institution-link">
                                        <MdSchool className="institution-icon" />
                                        <span className="institution-name">{education.institution}</span>
                                    </a>
                                    <div className="location-info">
                                        <FaMapMarkerAlt className="location-icon" />
                                        <span className="location-text">{education.location}</span>
                                    </div>
                                </div>
                                
                                <div className="duration-info">
                                    <BiTimeFive className="duration-icon" />
                                    <span className="duration-text">{education.duration}</span>
                                </div>
                                
                                <p className="education-description">{education.description}</p>
                                
                                <div className="grade-info">
                                    <FaAward className="grade-icon" />
                                    <span className="grade-text">{education.grade}</span>
                                </div>
                                
                                <div className="skills-section">
                                    <h4 className="skills-title">Key Skills & Subjects</h4>
                                    <div className="skills-tags">
                                        {education.skills.map((skill, skillIndex) => (
                                            <span key={skillIndex} className="skill-tag" style={{'--skill-color': education.color}}>
                                                {skill}
                                            </span>
                                        ))}
                                    </div>
                                </div>
                            </div>
                        </div>
                    );
                })}
            </div>

            <div className="education-stats">
                <div className="stat-item">
                    <div className="stat-icon">
                        <FaGraduationCap />
                    </div>
                    <div className="stat-content">
                        <span className="stat-number">3+</span>
                        <span className="stat-label">Qualifications</span>
                    </div>
                </div>
                
                <div className="stat-item">
                    <div className="stat-icon">
                        <FaCode />
                    </div>
                    <div className="stat-content">
                        <span className="stat-number">1000+</span>
                        <span className="stat-label">Hours Studied</span>
                    </div>
                </div>
                
                <div className="stat-item">
                    <div className="stat-icon">
                        <FaAward />
                    </div>
                    <div className="stat-content">
                        <span className="stat-number">100%</span>
                        <span className="stat-label">Completion Rate</span>
                    </div>
                </div>
            </div>
        </section>
    )
}

export default Education;
