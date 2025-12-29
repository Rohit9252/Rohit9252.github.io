import { useRef, useCallback,  } from 'react'

export const useDebouncedCallback = <F extends Function>(callback: F, delay: number) => {
  const timeout = useRef<ReturnType<typeof setTimeout>>()

  return useCallback(
    (...args: any[]) => {
      const handler = () => {
        clearTimeout(timeout.current)
        callback(...args)
      }

      clearTimeout(timeout.current)
      timeout.current = setTimeout(handler, delay)
    },
    [callback, delay],
  )
}
