import React, { useState } from 'react';
import './workExperience.css';
import { workExperienceData } from './experienceData';
import { FaBuilding, FaCalendarAlt, FaMapMarkerAlt, FaCode, FaTrophy } from 'react-icons/fa';
import { MdWork } from 'react-icons/md';

const WorkExperience = () => {
  const [selectedExperience, setSelectedExperience] = useState(0);

  return (
    <section id="work-experience">
      <h4>My Professional</h4>
      <h1>Work Experience</h1>
      
      <div className="experience-container">
        <div className="experience-timeline">
          {workExperienceData.map((exp, index) => (
            <div 
              key={exp.id}
              className={`timeline-item ${selectedExperience === index ? 'active' : ''}`}
              onClick={() => setSelectedExperience(index)}
            >
              <div className="timeline-dot"></div>
              <div className="timeline-content">
                <h3>{exp.company}</h3>
                <p>{exp.position}</p>
                <span className="duration">{exp.duration}</span>
              </div>
            </div>
          ))}
        </div>

        <div className="experience-details">
          {workExperienceData[selectedExperience] && (
            <div className="experience-card">
              <div className="experience-header">
                <div className="company-info">
                  <h2>{workExperienceData[selectedExperience].company}</h2>
                  <h3>{workExperienceData[selectedExperience].position}</h3>
                </div>
                <div className="experience-meta">
                  <div className="meta-item">
                    <FaCalendarAlt className="meta-icon" />
                    <span>{workExperienceData[selectedExperience].duration}</span>
                  </div>
                  <div className="meta-item">
                    <FaMapMarkerAlt className="meta-icon" />
                    <span>{workExperienceData[selectedExperience].location}</span>
                  </div>
                  <div className="meta-item">
                    <MdWork className="meta-icon" />
                    <span>{workExperienceData[selectedExperience].type}</span>
                  </div>
                </div>
              </div>

              <div className="experience-description">
                <p>{workExperienceData[selectedExperience].description}</p>
              </div>

              <div className="experience-section">
                <h4><FaBuilding className="section-icon" /> Key Responsibilities</h4>
                <ul className="responsibilities-list">
                  {workExperienceData[selectedExperience].responsibilities.map((responsibility, index) => (
                    <li key={index}>{responsibility}</li>
                  ))}
                </ul>
              </div>

              <div className="experience-section">
                <h4><FaCode className="section-icon" /> Tech Stack</h4>
                <div className="tech-stack">
                  {workExperienceData[selectedExperience].techStack.map((tech, index) => (
                    <span key={index} className="tech-tag">{tech}</span>
                  ))}
                </div>
              </div>

              <div className="experience-section">
                <h4><FaTrophy className="section-icon" /> Key Achievements</h4>
                <ul className="achievements-list">
                  {workExperienceData[selectedExperience].achievements.map((achievement, index) => (
                    <li key={index}>{achievement}</li>
                  ))}
                </ul>
              </div>
            </div>
          )}
        </div>
      </div>
    </section>
  );
};

export default WorkExperience;