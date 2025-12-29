import React from "react";
import {BsLinkedin} from "react-icons/bs";
import {RiWhatsappFill} from "react-icons/ri";
import {FaGithub} from "react-icons/fa";

const HeaderSocials = () => {
  return (
    <div>
      <div className="header__socials fade-in-left animate-in">
        <a href="https://www.linkedin.com/in/rohit-kumar-3b02451b8/" target="_blank" className="hover-lift pulse">
          <BsLinkedin />
        </a>
        <a href="https://github.com/Rohit9252" target="_blank" className="hover-lift pulse">
          <FaGithub />
        </a>
        <a
          target="_blank"
          href="https://api.whatsapp.com/send?phone=919056233995"
          className="hover-lift pulse"
        >
          <RiWhatsappFill />
        </a>
      </div>
    </div>
  );
};

export default HeaderSocials;
