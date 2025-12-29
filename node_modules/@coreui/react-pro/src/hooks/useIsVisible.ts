import { RefObject, useEffect, useState } from 'react'

export const useIsVisible = (ref: RefObject<HTMLElement>) => {
  const [isIntersecting, setIntersecting] = useState(false)

  useEffect(() => {
    const observer = new IntersectionObserver(([entry]) => setIntersecting(entry.isIntersecting))

    ref.current && observer.observe(ref.current)
    return () => observer.disconnect()
  }, [])

  return isIntersecting
}
