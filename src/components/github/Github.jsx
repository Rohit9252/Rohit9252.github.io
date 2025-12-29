import React from "react";
import { useEffect, useRef, useState } from "react";
import GitHubCalendar from "react-github-calendar";
import {Helmet} from "react-helmet";
import "./git.css";

const Github = () => {
  const [isVisible, setIsVisible] = useState(false);
  const githubRef = useRef(null);

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

    if (githubRef.current) {
      observer.observe(githubRef.current);
    }

    return () => observer.disconnect();
  }, []);

  return (
    <section id="gitHub" ref={githubRef}>
      <h5 className={`fade-in-up ${isVisible ? 'animate-in' : ''}`}>My</h5>
      <h1 className={`fade-in-up ${isVisible ? 'animate-in' : ''}`}>GitHub Calendar</h1>
      <div className={`git_calendar fade-in-up ${isVisible ? 'animate-in' : ''}`}>
        <GitHubCalendar username="rohit9252" />

        {/* </p> */}
      </div>
      <div className={`main_stats fade-in-up ${isVisible ? 'animate-in' : ''}`}>
        <img className={`scale-in ${isVisible ? 'animate-in' : ''}`} src="http://github-profile-summary-cards.vercel.app/api/cards/profile-details?username=rohit9252&theme=solarized_dark" />{" "}
        <div className="stats">
          <div className={`stagger-item ${isVisible ? 'animate-in' : ''}`}>  <img src="http://github-profile-summary-cards.vercel.app/api/cards/repos-per-language?username=rohit9252&theme=solarized_dark" /></div>
          <div className={`stagger-item ${isVisible ? 'animate-in' : ''}`}>     <img src="http://github-profile-summary-cards.vercel.app/api/cards/most-commit-language?username=rohit9252&theme=solarized_dark" /></div>
          <div className={`stagger-item ${isVisible ? 'animate-in' : ''}`}>
          <img src="http://github-profile-summary-cards.vercel.app/api/cards/stats?username=rohit9252&theme=solarized_dark" /></div>
          <div className={`stagger-item ${isVisible ? 'animate-in' : ''}`}><img src="http://github-profile-summary-cards.vercel.app/api/cards/productive-time?username=rohit9252&theme=solarized_dark&utcOffset=8" /></div>
        </div>
      </div>
    </section>
  );
};

export default Github;
