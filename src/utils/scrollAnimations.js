// Scroll Animation Utility
export const useScrollAnimation = (ref, callback, options = {}) => {
  const defaultOptions = {
    threshold: 0.1,
    rootMargin: '0px 0px -50px 0px',
    triggerOnce: true,
    ...options
  };

  const observer = new IntersectionObserver((entries) => {
    entries.forEach((entry) => {
      if (entry.isIntersecting) {
        callback(entry.target);
        if (defaultOptions.triggerOnce) {
          observer.unobserve(entry.target);
        }
      }
    });
  }, defaultOptions);

  if (ref.current) {
    observer.observe(ref.current);
  }

  return () => {
    if (ref.current) {
      observer.unobserve(ref.current);
    }
  };
};

// Animation classes utility
export const addScrollAnimations = () => {
  const observer = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          entry.target.classList.add('animate-in');
          // Optional: unobserve after animation triggers
          observer.unobserve(entry.target);
        }
      });
    },
    {
      threshold: 0.1,
      rootMargin: '0px 0px -50px 0px'
    }
  );

  // Observe all elements with animation classes
  const animatedElements = document.querySelectorAll(
    '.animate-on-scroll, .fade-in-up, .fade-in-left, .fade-in-right, .fade-in-down, .scale-in, .slide-in-left, .slide-in-right, .bounce-in, .rotate-in, .slide-in-bottom, .flip-in'
  );
  
  animatedElements.forEach((el) => observer.observe(el));

  return () => observer.disconnect();
};

// Staggered animations utility
export const addStaggeredAnimations = (containerSelector, itemSelector, delay = 100) => {
  const observer = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          const items = entry.target.querySelectorAll(itemSelector);
          items.forEach((item, index) => {
            setTimeout(() => {
              item.classList.add('animate-in');
            }, index * delay);
          });
          observer.unobserve(entry.target);
        }
      });
    },
    {
      threshold: 0.1,
      rootMargin: '0px 0px -100px 0px'
    }
  );

  const containers = document.querySelectorAll(containerSelector);
  containers.forEach((container) => observer.observe(container));

  return () => observer.disconnect();
};