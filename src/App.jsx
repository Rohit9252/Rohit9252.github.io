import "./App.css";
import About from "./components/about/About";
import Contact from "./components/contact/Contact";
import Education from "./components/education/Education";
import Skills from "./components/Skills/Skills";
import Github from "./components/github/Github";
import WorkExperience from "./components/workExperience/WorkExperience";
import Nav from "./components/Navbar/Nav";
import Projects from "./components/projects/Projects";
import ResumeDownloader from "./components/ResumeDownloader/ResumeDownloader";
import { useEffect } from "react";
import { addScrollAnimations } from "./utils/scrollAnimations";

function App() {
  useEffect(() => {
    // Initialize scroll animations
    const cleanup = addScrollAnimations();

    // Add staggered animations for specific containers
    const staggerContainers = document.querySelectorAll(".stagger-container");
    staggerContainers.forEach((container) => {
      const items = container.querySelectorAll(".stagger-item");
      items.forEach((item, index) => {
        item.style.transitionDelay = `${index * 0.1}s`;
      });
    });

    return cleanup;
  }, []);

  return (
    <div className="App">
      <ResumeDownloader />
      <Nav />
      <About />
      <WorkExperience />
      <Skills />
      <Education />
      <Projects />
      <Github />
      <Contact />
    </div>
  );
}

export default App;
