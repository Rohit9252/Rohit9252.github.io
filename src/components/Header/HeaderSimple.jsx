import React, { useEffect, useState } from "react";
import CTA from "./CTA";
import HeaderSocials from "./HeaderSocials";

const HeaderSimple = () => {
  const [displayedText, setDisplayedText] = useState("");
  const [roleIndex, setRoleIndex] = useState(0);
  const [charIndex, setCharIndex] = useState(0);
  const [isDeleting, setIsDeleting] = useState(false);
  
  const roles = [
    "Java Backend Developer",
    "Full Stack Developer", 
    "Software Engineer",
    "Problem Solver"
  ];
  
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
  
  return (
    <>
      <header>
        <div className="container header__container">
          <h3 className="greeting-simple">Hello, I'm</h3>
          <h1 className="name-simple">Rohit Kumar</h1>
          <h2 className="role-simple">
            I'm a <span className="typing-simple">{displayedText}</span>
            <span className="cursor-simple">|</span>
          </h2>
          <CTA />
          <HeaderSocials />
        </div>
      </header>
      
      <style jsx>{`
        .greeting-simple {
          font-size: 1.2rem;
          font-weight: 400;
          color: var(--color-light);
          margin-bottom: 0.5rem;
          animation: fadeIn 0.8s ease;
        }
        
        .name-simple {
          font-family: "Poppins", sans-serif;
          font-weight: 800;
          font-size: clamp(2.5rem, 6vw, 4rem);
          color: var(--color-primary);
          margin: 0 0 1rem 0;
          animation: slideInUp 1s ease;
        }
        
        .role-simple {
          font-family: "Inter", sans-serif;
          font-weight: 600;
          font-size: clamp(1.1rem, 3vw, 1.4rem);
          color: var(--color-light);
          margin: 0 0 2rem 0;
        }
        
        .typing-simple {
          color: var(--color-primary);
          font-weight: 700;
        }
        
        .cursor-simple {
          color: var(--color-primary);
          animation: blink 1s infinite;
        }
        
        @keyframes fadeIn {
          from { opacity: 0; }
          to { opacity: 1; }
        }
        
        @keyframes slideInUp {
          from {
            opacity: 0;
            transform: translateY(30px);
          }
          to {
            opacity: 1;
            transform: translateY(0);
          }
        }
        
        @keyframes blink {
          0%, 50% { opacity: 1; }
          51%, 100% { opacity: 0; }
        }
      `}</style>
    </>
  );
};

export default HeaderSimple;