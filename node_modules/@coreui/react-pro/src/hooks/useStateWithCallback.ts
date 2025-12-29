import { Dispatch, SetStateAction, useEffect, useState } from 'react'

export const useStateWithCallback = <S>(
  initialState: S,
  handler?: (prevState: S) => void,
  runHandler?: boolean,
): [S, Dispatch<SetStateAction<S>>] => {
  const [state, setState] = useState(initialState)
  handler &&
    useEffect(() => {
      runHandler && handler(state)
    }, [state])
  return [state, setState]
}
