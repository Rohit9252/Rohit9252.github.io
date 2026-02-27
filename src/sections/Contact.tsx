import { useEffect, useRef, useState } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import emailjs from '@emailjs/browser';
import { Mail, Phone, MapPin, Send, Linkedin, Github, Twitter, CheckCircle, AlertCircle, Loader2 } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Textarea } from '@/components/ui/textarea';
import { toast } from 'sonner';

gsap.registerPlugin(ScrollTrigger);

const contactInfo = [
  {
    icon: Mail,
    label: 'Email',
    value: 'rohitbatra0165@gmail.com',
    href: 'mailto:rohitbatra0165@gmail.com',
  },
  {
    icon: Phone,
    label: 'Phone',
    value: '+91-9056233995',
    href: 'tel:+919056233995',
  },
  {
    icon: MapPin,
    label: 'Location',
    value: 'Abohar, Punjab, India',
    href: '#',
  },
];

const socialLinks = [
  { icon: Linkedin, href: 'https://linkedin.com/in/rohit-kumar-3b02451b8/', label: 'LinkedIn' },
  { icon: Github, href: 'https://github.com/Rohit9252', label: 'GitHub' },
  { icon: Twitter, href: '#', label: 'Twitter' },
];

// EmailJS Configuration
const EMAILJS_CONFIG = {
  SERVICE_ID: 'service_85kyn8b',
  TEMPLATE_ID: 'template_y5vbh78',
  PUBLIC_KEY: 'c8GM-Q0oRjalII6f1',
};

interface FormErrors {
  fullName?: string;
  email?: string;
  subject?: string;
  message?: string;
}

export default function Contact() {
  const sectionRef = useRef<HTMLElement>(null);
  const headingRef = useRef<HTMLDivElement>(null);
  const formRef = useRef<HTMLFormElement>(null);
  const infoRef = useRef<HTMLDivElement>(null);
  
  const [formState, setFormState] = useState({
    fullName: '',
    email: '',
    subject: '',
    message: '',
  });
  const [errors, setErrors] = useState<FormErrors>({});
  const [touched, setTouched] = useState<Record<string, boolean>>({});
  const [isSubmitting, setIsSubmitting] = useState(false);
  const [isSubmitted, setIsSubmitted] = useState(false);
  const [submitError, setSubmitError] = useState<string | null>(null);

  useEffect(() => {
    const ctx = gsap.context(() => {
      gsap.fromTo(
        headingRef.current,
        { y: 50, opacity: 0 },
        {
          y: 0,
          opacity: 1,
          duration: 0.8,
          ease: 'expo.out',
          scrollTrigger: {
            trigger: headingRef.current,
            start: 'top 80%',
            toggleActions: 'play none none reverse',
          },
        }
      );

      gsap.fromTo(
        formRef.current,
        { x: -50, opacity: 0 },
        {
          x: 0,
          opacity: 1,
          duration: 0.8,
          ease: 'expo.out',
          scrollTrigger: {
            trigger: formRef.current,
            start: 'top 70%',
            toggleActions: 'play none none reverse',
          },
        }
      );

      gsap.fromTo(
        infoRef.current,
        { x: 50, opacity: 0 },
        {
          x: 0,
          opacity: 1,
          duration: 0.8,
          ease: 'expo.out',
          scrollTrigger: {
            trigger: infoRef.current,
            start: 'top 70%',
            toggleActions: 'play none none reverse',
          },
        }
      );
    }, sectionRef);

    return () => ctx.revert();
  }, []);

  // Validate a single field
  const validateField = (name: string, value: string): string | undefined => {
    const trimmedValue = value.trim();
    
    switch (name) {
      case 'fullName':
        if (!trimmedValue) return 'Full name is required';
        if (trimmedValue.length < 2) return 'Name must be at least 2 characters';
        if (trimmedValue.length > 50) return 'Name must be less than 50 characters';
        if (!/^[a-zA-Z\s]+$/.test(trimmedValue)) return 'Name should contain only letters';
        return undefined;
        
      case 'email':
        if (!trimmedValue) return 'Email is required';
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(trimmedValue)) return 'Please enter a valid email address';
        return undefined;
        
      case 'subject':
        if (!trimmedValue) return 'Subject is required';
        if (trimmedValue.length < 5) return 'Subject must be at least 5 characters';
        if (trimmedValue.length > 100) return 'Subject must be less than 100 characters';
        return undefined;
        
      case 'message':
        if (!trimmedValue) return 'Message is required';
        if (trimmedValue.length < 20) return 'Message must be at least 20 characters';
        if (trimmedValue.length > 1000) return 'Message must be less than 1000 characters';
        return undefined;
        
      default:
        return undefined;
    }
  };

  // Validate all fields
  const validateForm = (): boolean => {
    const newErrors: FormErrors = {};
    let isValid = true;

    (Object.keys(formState) as Array<keyof typeof formState>).forEach((key) => {
      const error = validateField(key, formState[key]);
      if (error) {
        newErrors[key] = error;
        isValid = false;
      }
    });

    setErrors(newErrors);
    return isValid;
  };

  const handleChange = (e: React.ChangeEvent<HTMLInputElement | HTMLTextAreaElement>) => {
    const { name, value } = e.target;
    setFormState((prev) => ({ ...prev, [name]: value }));
    
    // Validate on change if field was touched
    if (touched[name]) {
      const error = validateField(name, value);
      setErrors((prev) => ({ ...prev, [name]: error }));
    }
    
    setSubmitError(null);
  };

  const handleBlur = (e: React.FocusEvent<HTMLInputElement | HTMLTextAreaElement>) => {
    const { name, value } = e.target;
    setTouched((prev) => ({ ...prev, [name]: true }));
    const error = validateField(name, value);
    setErrors((prev) => ({ ...prev, [name]: error }));
  };

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    
    // Mark all fields as touched
    setTouched({ fullName: true, email: true, subject: true, message: true });
    
    // Validate form
    if (!validateForm()) {
      return;
    }

    setIsSubmitting(true);
    setSubmitError(null);
    
    try {
      // Check if EmailJS is configured
      if (
        EMAILJS_CONFIG.SERVICE_ID === 'YOUR_SERVICE_ID' ||
        EMAILJS_CONFIG.TEMPLATE_ID === 'YOUR_TEMPLATE_ID' ||
        EMAILJS_CONFIG.PUBLIC_KEY === 'YOUR_PUBLIC_KEY'
      ) {
        // EmailJS not configured - simulate success for demo
        console.log('EmailJS not configured. Form data:', formState);
        await new Promise((resolve) => setTimeout(resolve, 1500));
      } else {
        // Send email using EmailJS
        await emailjs.send(
          EMAILJS_CONFIG.SERVICE_ID,
          EMAILJS_CONFIG.TEMPLATE_ID,
          {
            name: formState.fullName,
            email: formState.email,
            title: formState.subject,
            message: formState.message,
            timestamp: new Date().toLocaleString(),
            to_name: 'Rohit Kumar',
          },
          EMAILJS_CONFIG.PUBLIC_KEY
        );
      }
      
      setIsSubmitting(false);
      setIsSubmitted(true);
      toast.success("📧 Email sent successfully! I'll get back to you soon.");
      setFormState({ fullName: '', email: '', subject: '', message: '' });
      setTouched({});
      setErrors({});
      
      // Reset success message after 5 seconds
      setTimeout(() => setIsSubmitted(false), 5000);
    } catch (err) {
      setIsSubmitting(false);
      const errorMsg = 'Failed to send message. Please try again or contact me directly via email.';
      setSubmitError(errorMsg);
      toast.error("❌ " + errorMsg);
      console.error('EmailJS Error:', err);
    }
  };

  const getInputClassName = (fieldName: string) => {
    const baseClass = 'rounded-xl bg-secondary/50 border-0 focus:ring-2 focus:ring-[#5B8DF7] h-12 transition-all';
    if (touched[fieldName] && errors[fieldName as keyof FormErrors]) {
      return `${baseClass} ring-2 ring-red-500 focus:ring-red-500`;
    }
    if (touched[fieldName] && !errors[fieldName as keyof FormErrors]) {
      return `${baseClass} ring-2 ring-green-500 focus:ring-[#5B8DF7]`;
    }
    return baseClass;
  };

  return (
    <section
      ref={sectionRef}
      id="contact"
      className="relative py-24 sm:py-32 overflow-hidden"
    >
      {/* Background */}
      <div className="absolute inset-0 pointer-events-none">
        <div className="absolute top-0 left-0 w-full h-full bg-gradient-to-br from-[#5B8DF7]/5 via-transparent to-purple-500/5" />
        <div className="absolute bottom-1/4 right-1/4 w-96 h-96 bg-[#5B8DF7]/5 rounded-full blur-3xl" />
      </div>

      <div className="container mx-auto px-4 sm:px-6 lg:px-8 relative z-10">
        {/* Section Header */}
        <div ref={headingRef} className="text-center mb-16">
          <span className="inline-block px-4 py-1.5 rounded-full glass text-sm font-medium text-[#5B8DF7] mb-4">
            Get In Touch
          </span>
          <h2 className="text-3xl sm:text-4xl md:text-5xl font-bold tracking-tight mb-4">
            Let's Work <span className="text-gradient">Together</span>
          </h2>
          <p className="text-lg text-muted-foreground max-w-2xl mx-auto">
            Have a project in mind or want to discuss opportunities? I'd love to hear from you.
          </p>
        </div>

        <div className="grid lg:grid-cols-2 gap-12 lg:gap-16 max-w-5xl mx-auto">
          {/* Contact Form */}
          <form
            ref={formRef}
            onSubmit={handleSubmit}
            className="glass rounded-2xl p-6 sm:p-8 space-y-5"
            noValidate
          >
            {/* Full Name */}
            <div>
              <label htmlFor="fullName" className="block text-sm font-medium mb-2">
                Full Name <span className="text-red-500">*</span>
              </label>
              <Input
                id="fullName"
                name="fullName"
                type="text"
                placeholder="John Doe"
                value={formState.fullName}
                onChange={handleChange}
                onBlur={handleBlur}
                className={getInputClassName('fullName')}
              />
              {touched.fullName && errors.fullName && (
                <p className="text-red-500 text-xs mt-1 flex items-center gap-1">
                  <AlertCircle className="h-3 w-3" />
                  {errors.fullName}
                </p>
              )}
            </div>

            {/* Email */}
            <div>
              <label htmlFor="email" className="block text-sm font-medium mb-2">
                Email Address <span className="text-red-500">*</span>
              </label>
              <Input
                id="email"
                name="email"
                type="email"
                placeholder="john@example.com"
                value={formState.email}
                onChange={handleChange}
                onBlur={handleBlur}
                className={getInputClassName('email')}
              />
              {touched.email && errors.email && (
                <p className="text-red-500 text-xs mt-1 flex items-center gap-1">
                  <AlertCircle className="h-3 w-3" />
                  {errors.email}
                </p>
              )}
            </div>

            {/* Subject */}
            <div>
              <label htmlFor="subject" className="block text-sm font-medium mb-2">
                Subject <span className="text-red-500">*</span>
              </label>
              <Input
                id="subject"
                name="subject"
                type="text"
                placeholder="Project Inquiry / Job Opportunity"
                value={formState.subject}
                onChange={handleChange}
                onBlur={handleBlur}
                className={getInputClassName('subject')}
              />
              {touched.subject && errors.subject && (
                <p className="text-red-500 text-xs mt-1 flex items-center gap-1">
                  <AlertCircle className="h-3 w-3" />
                  {errors.subject}
                </p>
              )}
            </div>

            {/* Message */}
            <div>
              <label htmlFor="message" className="block text-sm font-medium mb-2">
                Your Message <span className="text-red-500">*</span>
              </label>
              <Textarea
                id="message"
                name="message"
                placeholder="Tell me about your project, requirements, or any questions you have..."
                value={formState.message}
                onChange={handleChange}
                onBlur={handleBlur}
                rows={5}
                className={`${getInputClassName('message')} h-auto resize-none`}
              />
              <div className="flex justify-between items-center mt-1">
                {touched.message && errors.message ? (
                  <p className="text-red-500 text-xs flex items-center gap-1">
                    <AlertCircle className="h-3 w-3" />
                    {errors.message}
                  </p>
                ) : (
                  <span />
                )}
                <span className={`text-xs ${
                  formState.message.length > 1000 ? 'text-red-500' : 'text-muted-foreground'
                }`}>
                  {formState.message.length}/1000
                </span>
              </div>
            </div>

            {/* Submit Error */}
            {submitError && (
              <div className="flex items-center gap-2 text-red-500 text-sm p-3 rounded-xl bg-red-500/10">
                <AlertCircle className="h-4 w-4 flex-shrink-0" />
                <span>{submitError}</span>
              </div>
            )}

            {/* Submit Button */}
            <Button
              type="submit"
              disabled={isSubmitting || isSubmitted}
              className={`w-full rounded-xl py-6 transition-all duration-300 ${
                isSubmitted
                  ? 'bg-green-500 hover:bg-green-600'
                  : 'bg-[#5B8DF7] hover:bg-[#4a7de6]'
              } text-white h-12`}
            >
              {isSubmitting ? (
                <span className="flex items-center gap-2">
                  <Loader2 className="h-5 w-5 animate-spin" />
                  Sending...
                </span>
              ) : isSubmitted ? (
                <span className="flex items-center gap-2">
                  <CheckCircle className="h-5 w-5" />
                  Message Sent Successfully!
                </span>
              ) : (
                <span className="flex items-center gap-2">
                  <Send className="h-5 w-5" />
                  Send Message
                </span>
              )}
            </Button>

            {/* Note about EmailJS setup */}
            {EMAILJS_CONFIG.SERVICE_ID === 'YOUR_SERVICE_ID' && (
              <p className="text-xs text-muted-foreground text-center">
                Note: Configure EmailJS to enable email functionality.{' '}
                <a 
                  href="https://www.emailjs.com/docs/" 
                  target="_blank" 
                  rel="noopener noreferrer"
                  className="text-[#5B8DF7] hover:underline"
                >
                  Learn more
                </a>
              </p>
            )}
          </form>

          {/* Contact Info */}
          <div ref={infoRef} className="space-y-8">
            {/* Info Cards */}
            <div className="space-y-4">
              {contactInfo.map((info) => (
                <a
                  key={info.label}
                  href={info.href}
                  className="flex items-center gap-4 p-4 rounded-xl glass hover:bg-[#5B8DF7]/10 transition-colors group"
                >
                  <div className="w-12 h-12 rounded-xl bg-[#5B8DF7]/20 flex items-center justify-center group-hover:bg-[#5B8DF7] transition-colors flex-shrink-0">
                    <info.icon className="h-5 w-5 text-[#5B8DF7] group-hover:text-white" />
                  </div>
                  <div className="min-w-0">
                    <p className="text-sm text-muted-foreground">{info.label}</p>
                    <p className="font-medium truncate">{info.value}</p>
                  </div>
                </a>
              ))}
            </div>

            {/* Social Links */}
            <div>
              <h3 className="text-sm font-semibold uppercase tracking-wider text-muted-foreground mb-4">
                Connect With Me
              </h3>
              <div className="flex gap-3">
                {socialLinks.map((social) => (
                  <a
                    key={social.label}
                    href={social.href}
                    target="_blank"
                    rel="noopener noreferrer"
                    className="w-12 h-12 rounded-xl glass flex items-center justify-center hover:bg-[#5B8DF7] hover:text-white transition-all duration-300"
                    aria-label={social.label}
                  >
                    <social.icon className="h-5 w-5" />
                  </a>
                ))}
              </div>
            </div>

            {/* Availability Card */}
            <div className="glass rounded-2xl p-6">
              <div className="flex items-center gap-3 mb-4">
                <span className="w-3 h-3 rounded-full bg-green-500 animate-pulse" />
                <span className="font-semibold">Available for Work</span>
              </div>
              <p className="text-sm text-muted-foreground">
                I'm currently open to new opportunities and interesting projects. 
                Feel free to reach out if you'd like to collaborate!
              </p>
            </div>

            {/* Quick Response Promise */}
            <div className="glass rounded-2xl p-6 border-l-4 border-[#5B8DF7]">
              <h4 className="font-semibold mb-2">Quick Response</h4>
              <p className="text-sm text-muted-foreground">
                I typically respond to all inquiries within 24-48 hours. For urgent matters, 
                please reach out via phone or LinkedIn.
              </p>
            </div>
          </div>
        </div>
      </div>
    </section>
  );
}
