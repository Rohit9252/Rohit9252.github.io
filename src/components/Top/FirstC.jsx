import React from 'react'
import Header from '../Header/Header'
import MainImage from '../Header/Image'
import { FaDownload } from 'react-icons/fa'
import "./FirstC.css"
import cv from "../../assets/Rohit_Kumar.pdf"

const FirstC = () => {
  const handleDownloadResume = () => {
    const link = document.createElement('a');
    link.href = cv;
    link.download = 'Rohit_Kumar_Resume.pdf';
    link.click();
  };

  return (
    <>
      <div className="particles">
        <div className='chng_ico'>
          <button 
            onClick={handleDownloadResume}
            className="resume-icon pulse-glow hover-lift"
            title="Download Resume"
          >
            <FaDownload />
          </button>
        </div>
        
        <div className="TOP__one fade-in-up animate-in">
          <div>
            <Header />
          </div>
          <div className="float"><MainImage /></div>
        </div>
      </div>
    </>
  );
}

export default FirstC