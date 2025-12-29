import React, { useEffect, useRef } from 'react'
import "./Projects.css"
import { data } from "./data"
import { SiNetlify } from "react-icons/si"
import { FaGithubAlt, FaExternalLinkAlt } from "react-icons/fa"
import { BiCode } from "react-icons/bi"

const Projects = () => {
    const projectsRef = useRef(null);

    useEffect(() => {
        const observer = new IntersectionObserver(
            (entries) => {
                entries.forEach((entry) => {
                    if (entry.isIntersecting) {
                        entry.target.classList.add('animate-in');
                    }
                });
            },
            { threshold: 0.1, rootMargin: '0px 0px -50px 0px' }
        );

        const projectCards = document.querySelectorAll('.project-card');
        projectCards.forEach((card) => observer.observe(card));

        return () => observer.disconnect();
    }, []);

    return (
        <section id='projects' className='projects-section'>
            <div className='projects-header'>
                <span className='section-subtitle'>My Recent Work</span>
                <h1 className='section-title'>Featured Projects</h1>
                <p className='section-description'>
                    Here are some of my favorite projects I've worked on, showcasing my skills in modern web development.
                </p>
            </div>
            
            <div className="projects-grid" ref={projectsRef}>
                {data.map((project, index) => {
                    return (
                        <div className={`project-card card-${index + 1}`} key={index}>
                            <div className='project-image-container'>
                                <img 
                                    src={project.img} 
                                    alt={project.title}
                                    className='project-image'
                                    loading='lazy'
                                />
                                <div className='image-overlay'>
                                    <div className='overlay-buttons'>
                                        <a href={project.live} target="_blank" rel="noopener noreferrer" className='overlay-btn live-btn' title="View Live Demo">
                                            <FaExternalLinkAlt />
                                        </a>
                                        <a href={project.git} target="_blank" rel="noopener noreferrer" className='overlay-btn github-btn' title="View Source Code">
                                            <BiCode />
                                        </a>
                                    </div>
                                </div>
                            </div>
                            
                            <div className='project-content'>
                                <div className='project-header'>
                                    <h3 className='project-title'>{project.title}</h3>
                                    {project.g && <span className='project-type'>{project.g}</span>}
                                </div>
                                
                                <p className='project-description'>{project.desc}</p>
                                
                                <div className='tech-stack'>
                                    <span className='tech-label'>Tech Stack:</span>
                                    <div className='tech-tags'>
                                        {project.lang.split(', ').map((tech, techIndex) => (
                                            <span key={techIndex} className='tech-tag'>{tech}</span>
                                        ))}
                                    </div>
                                </div>
                                
                                <div className='project-links'>
                                    <a href={project.live} target="_blank" rel="noopener noreferrer" className='project-link primary-link'>
                                        <SiNetlify className='link-icon'/>
                                        <span>Live Demo</span>
                                    </a>
                                    <a href={project.git} target="_blank" rel="noopener noreferrer" className='project-link secondary-link'>
                                        <FaGithubAlt className='link-icon'/>
                                        <span>Source Code</span>
                                    </a>
                                </div>
                            </div>
                        </div>
                    )
                })}
            </div>
        </section>
    )
}
export default Projects;
