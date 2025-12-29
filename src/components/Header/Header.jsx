import React, { useEffect, useState } from "react";
import CTA from "./CTA";
import HeaderSocials from "./HeaderSocials";

const Header = () => {
  const [isVisible, setIsVisible] = useState(false);
  const [displayedText, setDisplayedText] = useState("");
  const [roleIndex, setRoleIndex] = useState(0);
  const [charIndex, setCharIndex] = useState(0);
  const [isDeleting, setIsDeleting] = useState(false);
  const [showCursor, setShowCursor] = useState(true);
  const [nameVisible, setNameVisible] = useState(false);
  const [roleVisible, setRoleVisible] = useState(false);
  
  const roles = [
    "Java Backend Developer",
    "Full Stack Developer",
    "Software Engineer",
    "Problem Solver"
  ];
  
  // Visibility animation
  useEffect(() => {
    const timer1 = setTimeout(() => setIsVisible(true), 200);
    const timer2 = setTimeout(() => setNameVisible(true), 600);
    const timer3 = setTimeout(() => setRoleVisible(true), 1000);
    
    return () => {
      clearTimeout(timer1);
      clearTimeout(timer2);
      clearTimeout(timer3);
    };
  }, []);
  
  // Typing animation for roles
  useEffect(() => {
    const currentRole = roles[roleIndex];
    const typingSpeed = isDeleting ? 100 : 150;
    const pauseTime = isDeleting ? 1000 : 2000;
    
    const timer = setTimeout(() => {
      if (!isDeleting && charIndex < currentRole.length) {
        setDisplayedText(currentRole.substring(0, charIndex + 1));
        setCharIndex(charIndex + 1);
      } else if (isDeleting && charIndex > 0) {
        setDisplayedText(currentRole.substring(0, charIndex - 1));
        setCharIndex(charIndex - 1);
      } else if (!isDeleting && charIndex === currentRole.length) {
        setTimeout(() => setIsDeleting(true), pauseTime);
      } else if (isDeleting && charIndex === 0) {
        setIsDeleting(false);
        setRoleIndex((roleIndex + 1) % roles.length);
      }
    }, typingSpeed);
    
    return () => clearTimeout(timer);
  }, [charIndex, isDeleting, roleIndex, roles]);
  
  // Cursor blinking animation
  useEffect(() => {
    const cursorTimer = setInterval(() => {
      setShowCursor(prev => !prev);
    }, 530);
    
    return () => clearInterval(cursorTimer);
  }, []);
  
  return (
    <>
      <header>
        <div className="container header__container">
          <div className={`greeting-container ${isVisible ? 'visible' : ''}`}>
            <span className="greeting-text">Hello, I'm</span>
            <div className="sparkle sparkle-1">✨</div>
            <div className="sparkle sparkle-2">⭐</div>
            <div className="sparkle sparkle-3">💫</div>
          </div>
          
          <div className={`name-container ${nameVisible ? 'visible' : ''}`}>
            <h1 className="name-text-simple">Rohit Kumar</h1>
            <div className="name-underline"></div>
          </div>
          
          <div className={`role-container ${roleVisible ? 'visible' : ''}`}>
            <h2 className="role-text">
              <span className="role-prefix">I'm a </span>
              <span className="typing-text">{displayedText}</span>
              <span className={`cursor ${showCursor ? 'blink' : ''}`}>|</span>
            </h2>
          </div>
          
          <div className={`cta-container ${roleVisible ? 'visible' : ''}`}>
            <CTA />
          </div>
          
          <div className={`socials-container ${roleVisible ? 'visible' : ''}`}>
            <HeaderSocials />
          </div>
        </div>
      </header>
    </>
  );
};

export default Header;
