import { Dispatch, SetStateAction } from 'react';
export declare const useStateWithCallback: <S>(initialState: S, handler?: ((prevState: S) => void) | undefined, runHandler?: boolean) => [S, Dispatch<SetStateAction<S>>];
