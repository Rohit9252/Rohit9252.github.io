import React, {useState} from "react";
import { useEffect, useRef } from "react";
import "./contact.css";
import {MdOutlineEmail} from "react-icons/md";
import {FaGithub} from "react-icons/fa";
import {BsLinkedin} from "react-icons/bs";
import emailjs from "emailjs-com";
import {ToastContainer, toast} from "react-toastify";
import "react-toastify/dist/ReactToastify.css";

const Contact = () => {
  const [loading, setLoading] = useState(false);
  const [isVisible, setIsVisible] = useState(false);
  const form = useRef();
  const contactRef = useRef(null);

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

    if (contactRef.current) {
      observer.observe(contactRef.current);
    }

    return () => observer.disconnect();
  }, []);

  const sendEmail = (e) => {
    e.preventDefault();
    setLoading(true);
    
    // Validate form data
    const formData = new FormData(form.current);
    const name = formData.get('name');
    const email = formData.get('email');
    const title = formData.get('title');
    const message = formData.get('message');
    formData.timestamp =new Date().toLocaleString();


    console.log({ name, email, title, message, timestamp: formData.timestamp });

    
    if (!name || !email || !title || !message || !formData.timestamp) {
      setLoading(false);
      toast("❌ Please fill in all fields", {
        position: "top-right",
        autoClose: 5000,
        hideProgressBar: false,
        closeOnClick: true,
        pauseOnHover: true,
        draggable: true,
        progress: undefined,
        type: "error",
        theme: "dark",
      });
      return;
    }

    // Email validation
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    if (!emailRegex.test(email)) {
      setLoading(false);
      toast("❌ Please enter a valid email address", {
        position: "top-right",
        autoClose: 5000,
        hideProgressBar: false,
        closeOnClick: true,
        pauseOnHover: true,
        draggable: true,
        progress: undefined,
        type: "error",
        theme: "dark",
      });
      return;
    }

    emailjs
      .sendForm(
        "service_85kyn8b",    // Your service ID
        "template_y5vbh78",   // Your template ID
        form.current,
        "c8GM-Q0oRjalII6f1"   // Your public key
      )
      .then(
        (result) => {
          console.log('Email sent successfully:', result.text);
          setLoading(false);
          toast("📧 Email sent successfully! I'll get back to you soon.", {
            position: "top-right",
            autoClose: 5000,
            hideProgressBar: false,
            closeOnClick: true,
            pauseOnHover: true,
            draggable: true,
            progress: undefined,
            type: "success",
            theme: "dark",
          });
          // Reset the form
          form.current.reset();
        },
        (error) => {
          setLoading(false);
          console.log('Email send error:', error.text);
          toast("❌ Failed to send email. Please try again or contact me directly.", {
            position: "top-right",
            autoClose: 5000,
            hideProgressBar: false,
            closeOnClick: true,
            pauseOnHover: true,
            draggable: true,
            progress: undefined,
            type: "error",
            theme: "dark",
          });
        }
      );
  };

  return (
    <div>
      <section id="contact" ref={contactRef}>
        <h5 className={`fade-in-up ${isVisible ? 'animate-in' : ''}`}>Get In Touch</h5>
        <h1 className={`fade-in-up ${isVisible ? 'animate-in' : ''}`}>Contact Me</h1>
        <div className="contact contact_container">
          <div className={`contact_options fade-in-left ${isVisible ? 'animate-in' : ''}`}>
            <div className={`contact_option stagger-item ${isVisible ? 'animate-in' : ''}`}>
              <article>
                <MdOutlineEmail className="contact_icon" />
                <h4>Email</h4>
                <h5>rohitbatra0165@gmail.com</h5>
                <a href="mailto:rohitbatra0165@gmail.com" target="_blank" rel="noopener noreferrer">
                  Send a message
                </a>
              </article>
            </div>
            
            <div className={`contact_option stagger-item ${isVisible ? 'animate-in' : ''}`}>
              <article>
                <BsLinkedin className="contact_icon" />
                <h4>LinkedIn</h4>
                <h5>Connect with me</h5>
                <a
                  target="_blank"
                  rel="noopener noreferrer"
                  href="https://www.linkedin.com/in/rohit-kumar-3b02451b8/"
                >
                  View Profile
                </a>
              </article>
            </div>
            
            <div className={`contact_option stagger-item ${isVisible ? 'animate-in' : ''}`}>
              <article>
                <FaGithub className="contact_icon" />
                <h4>GitHub</h4>
                <h5>View my projects</h5>
                <a
                  target="_blank"
                  rel="noopener noreferrer"
                  href="https://github.com/Rohit9252"
                >
                  View Repository
                </a>
              </article>
            </div>
          </div>
          <form ref={form} onSubmit={sendEmail} className={`fade-in-right ${isVisible ? 'animate-in' : ''}`}>
            <input
              type="text"
              name="name"
              placeholder="Your Full Name"
              required
            />
            <input
              type="email"
              name="email"
              placeholder="Your Email"
              required
            />
            <input
              type="text"
              name="title"
              placeholder="Subject/Title"
              required
            />
            <textarea
              name="message"
              placeholder="Your Message"
              rows="7"
              required
            ></textarea>

            <button disabled={loading} className="sendBtn" type="submit">
              {loading ? "Sending..." : "Send Message"}
            </button>
          </form>
          <ToastContainer />
        </div>
      </section>
    </div>
  );
};

export default Contact;