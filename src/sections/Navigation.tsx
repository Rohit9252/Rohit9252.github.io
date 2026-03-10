import { useEffect, useRef, useState } from 'react';
import { gsap } from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';
import { Sun, Moon, Menu, X, Download } from 'lucide-react';
import { useTheme } from '../hooks/useTheme';
import { Button } from '@/components/ui/button';

gsap.registerPlugin(ScrollTrigger);

const navLinks = [
  { name: 'Home', href: '#home' },
  { name: 'About', href: '#about' },
  { name: 'Experience', href: '#experience' },
  { name: 'Skills', href: '#skills' },
  { name: 'Certifications', href: '#certifications' },
  { name: 'Projects', href: '#projects' },
  { name: 'Contact', href: '#contact' },
];

export default function Navigation() {
  const { theme, toggleTheme } = useTheme();
  const [isScrolled, setIsScrolled] = useState(false);
  const [isMobileMenuOpen, setIsMobileMenuOpen] = useState(false);
  const navRef = useRef<HTMLElement>(null);
  const linksRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const handleScroll = () => {
      setIsScrolled(window.scrollY > 50);
    };

    window.addEventListener('scroll', handleScroll, { passive: true });
    return () => window.removeEventListener('scroll', handleScroll);
  }, []);

  useEffect(() => {
    // Entrance animation
    if (navRef.current) {
      gsap.fromTo(
        navRef.current,
        { y: -100, opacity: 0 },
        { y: 0, opacity: 1, duration: 0.8, delay: 0.2, ease: 'expo.out' }
      );
    }

    if (linksRef.current) {
      gsap.fromTo(
        linksRef.current.children,
        { opacity: 0, y: -10 },
        { opacity: 1, y: 0, duration: 0.4, stagger: 0.05, delay: 0.4 }
      );
    }
  }, []);

  // Close mobile menu on resize
  useEffect(() => {
    const handleResize = () => {
      if (window.innerWidth >= 768) {
        setIsMobileMenuOpen(false);
      }
    };

    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  // Prevent body scroll when mobile menu is open
  useEffect(() => {
    if (isMobileMenuOpen) {
      document.body.style.overflow = 'hidden';
    } else {
      document.body.style.overflow = '';
    }
    return () => {
      document.body.style.overflow = '';
    };
  }, [isMobileMenuOpen]);

  const scrollToSection = (href: string) => {
    const element = document.querySelector(href);
    if (element) {
      element.scrollIntoView({ behavior: 'smooth' });
    }
    setIsMobileMenuOpen(false);
  };

  return (
    <>
      <nav
        ref={navRef}
        className={`fixed top-0 left-0 right-0 z-50 transition-all duration-500 custom-expo ${
          isScrolled ? 'py-2' : 'py-4'
        }`}
      >
        <div className="container mx-auto px-4 sm:px-6 lg:px-8">
          <div
            className={`relative flex items-center justify-between px-4 sm:px-6 py-3 rounded-full transition-all duration-500 ${
              isScrolled
                ? 'glass shadow-lg max-w-5xl mx-auto'
                : 'bg-transparent max-w-6xl mx-auto'
            }`}
          >
            {/* Logo */}
            <a
              href="#home"
              onClick={(e) => {
                e.preventDefault();
                scrollToSection('#home');
              }}
              className="text-xl font-bold tracking-tight hover:text-[#5B8DF7] transition-colors flex-shrink-0"
            >
              RK
            </a>

            {/* Desktop Links */}
            <div
              ref={linksRef}
              className="hidden lg:flex items-center gap-1"
            >
              {navLinks.map((link) => (
                <a
                  key={link.name}
                  href={link.href}
                  onClick={(e) => {
                    e.preventDefault();
                    scrollToSection(link.href);
                  }}
                  className="relative px-3 py-1.5 text-sm font-medium text-muted-foreground hover:text-foreground transition-colors rounded-full hover:bg-secondary group whitespace-nowrap"
                >
                  {link.name}
                  <span className="absolute inset-0 rounded-full bg-[#5B8DF7]/10 scale-0 group-hover:scale-100 transition-transform duration-300" />
                </a>
              ))}
            </div>

            {/* Actions */}
            <div className="flex items-center gap-2 flex-shrink-0">
              <Button
                variant="ghost"
                size="icon"
                onClick={toggleTheme}
                className="rounded-full hover:bg-secondary w-9 h-9"
                aria-label="Toggle theme"
              >
                {theme === 'dark' ? (
                  <Sun className="h-4 w-4" />
                ) : (
                  <Moon className="h-4 w-4" />
                )}
              </Button>

              <a
                href="/Rohit_Kumar.pdf"
                download="Rohit_Kumar.pdf"
                className="hidden sm:flex"
              >
                <Button
                  variant="outline"
                  size="sm"
                  className="rounded-full border-[#5B8DF7] text-[#5B8DF7] hover:bg-[#5B8DF7] hover:text-white transition-all gap-2"
                >
                  <Download className="h-4 w-4" />
                  Resume
                </Button>
              </a>

              <Button
                className="hidden sm:flex rounded-full bg-[#5B8DF7] hover:bg-[#4a7de6] text-white text-sm px-4"
                onClick={() => scrollToSection('#contact')}
              >
                Let's Talk
              </Button>

              {/* Mobile Menu Button */}
              <Button
                variant="ghost"
                size="icon"
                className="lg:hidden rounded-full w-9 h-9"
                onClick={() => setIsMobileMenuOpen(!isMobileMenuOpen)}
                aria-label="Toggle menu"
              >
                {isMobileMenuOpen ? (
                  <X className="h-5 w-5" />
                ) : (
                  <Menu className="h-5 w-5" />
                )}
              </Button>
            </div>
          </div>
        </div>
      </nav>

      {/* Mobile Menu Overlay */}
      <div
        className={`fixed inset-0 z-40 lg:hidden transition-all duration-300 ${
          isMobileMenuOpen ? 'visible' : 'invisible'
        }`}
      >
        {/* Backdrop */}
        <div
          className={`absolute inset-0 bg-background/90 backdrop-blur-xl transition-opacity duration-300 ${
            isMobileMenuOpen ? 'opacity-100' : 'opacity-0'
          }`}
          onClick={() => setIsMobileMenuOpen(false)}
        />
        
        {/* Menu Content */}
        <div
          className={`absolute top-24 left-4 right-4 glass rounded-3xl p-8 transition-all duration-500 custom-expo shadow-2xl border border-white/10 ${
            isMobileMenuOpen 
              ? 'translate-y-0 opacity-100 scale-100' 
              : '-translate-y-10 opacity-0 scale-95'
          }`}
        >
          <div className="flex flex-col gap-2">
            {navLinks.map((link, index) => (
              <a
                key={link.name}
                href={link.href}
                onClick={(e) => {
                  e.preventDefault();
                  scrollToSection(link.href);
                }}
                className="px-6 py-4 text-xl font-semibold text-muted-foreground hover:text-[#5B8DF7] hover:bg-[#5B8DF7]/5 rounded-2xl transition-all duration-300 flex items-center justify-between group"
                style={{ 
                  transitionDelay: isMobileMenuOpen ? `${index * 40}ms` : '0ms' 
                }}
              >
                <span>{link.name}</span>
                <span className="w-1.5 h-1.5 rounded-full bg-[#5B8DF7] scale-0 group-hover:scale-100 transition-transform" />
              </a>
            ))}
            <div className="mt-4 pt-4 border-t border-border/50 flex flex-col gap-3">
              <a
                href="/Rohit_Kumar.pdf"
                download="Rohit_Kumar.pdf"
                className="w-full"
              >
                <Button
                  variant="outline"
                  className="w-full h-14 rounded-2xl border-[#5B8DF7]/30 text-[#5B8DF7] hover:bg-[#5B8DF7] hover:text-white transition-all gap-3 text-lg font-medium"
                >
                  <Download className="h-5 w-5" />
                  Download Resume
                </Button>
              </a>
              <Button
                className="w-full h-14 rounded-2xl bg-[#5B8DF7] hover:bg-[#4a7de6] text-white text-lg font-bold shadow-lg shadow-[#5B8DF7]/20"
                onClick={() => scrollToSection('#contact')}
              >
                Let's Talk
              </Button>
            </div>
          </div>
        </div>
      </div>
    </>
  );
}
