import React, { useState } from "react";
import { BiHome, BiBook, BiUser } from "react-icons/bi";
import { FcAbout } from "react-icons/fc";
import { MdContactMail, MdWork, MdSchool } from "react-icons/md";
import { RiServiceLine, RiGitRepositoryLine } from "react-icons/ri";
import { GiSkills } from "react-icons/gi";
import { FaBriefcase, FaGraduationCap } from "react-icons/fa";
import "./nav.css"

const NAv = () => {
  const [active, setActive] = useState("#")
  
  return (
    <div>
      <nav>
        <a href="#" className={active == "#" ? "active" : ""}
          onClick={() => setActive("#")}  >
          <BiHome />
        </a>
        <a href="#about" className={active == "#about" ? "active" : ""} onClick={() => setActive("#about")}>
          <FcAbout />
        </a>
        <a href="#education" className={active == "#education" ? "active" : ""} onClick={() => setActive("#education")}>
          <FaGraduationCap />
        </a>
        <a href="#skills" className={active == "#skills" ? "active" : ""} onClick={() => setActive("#skills")}>
          <GiSkills />
        </a>
        <a href="#work-experience" className={active == "#work-experience" ? "active" : ""} onClick={() => setActive("#work-experience")}>
          <FaBriefcase />
        </a>
        <a href="#projects" className={active == "#projects" ? "active" : ""} onClick={() => setActive("#projects")}>
          <RiServiceLine />
        </a>
        <a href="#gitHub" className={active == "#gitHub" ? "active" : ""} onClick={() => setActive("#gitHub")}>
          <RiGitRepositoryLine />
        </a>
        <a href="#contact" className={active == "#contact" ? "active" : ""} onClick={() => setActive("#contact")}>
          <MdContactMail />
        </a>
      </nav>
    </div>
  );
};

export default NAv;