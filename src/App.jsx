import './App.css'
import About from './components/about/About'
import Contact from './components/contact/Contact'
import Education from './components/education/Education'
import Experience from './components/experience/Experience'
import Github from './components/github/Github'
import WorkExperience from './components/workExperience/WorkExperience'
import NAv from './components/Navbar/NAv'
import Projects from './components/projects/Projects'
import FirstC from './components/Top/FirstC'
import { useEffect } from 'react'
import { addScrollAnimations } from './utils/scrollAnimations'

function App() {
  useEffect(() => {
    // Initialize scroll animations
    const cleanup = addScrollAnimations();
    
    // Add staggered animations for specific containers
    const staggerContainers = document.querySelectorAll('.stagger-container');
    staggerContainers.forEach(container => {
      const items = container.querySelectorAll('.stagger-item');
      items.forEach((item, index) => {
        item.style.transitionDelay = `${index * 0.1}s`;
      });
    });
    
    return cleanup;
  }, []);

  return (
    <div className="App">
      <FirstC />
      <NAv />
      <About />
      <Education />
      <Experience />
      <WorkExperience />
      <Projects />
      <Github />
      <Contact />

    </div>
  )
}

export default App
