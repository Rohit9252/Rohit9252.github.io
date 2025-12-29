import type { LocalizedTimePartials } from './types';
export declare const convert12hTo24h: (abbr: 'am' | 'pm', hour: number) => number;
export declare const convert24hTo12h: (hour: number) => number;
export declare const convertTimeToDate: (time: Date | string | null | undefined) => Date | null;
export declare const getAmPm: (date: Date, locale: string) => "am" | "pm";
export declare const getListOfHours: (locale: string, ampm?: 'auto' | boolean) => {
    value: number;
    label: string;
}[];
export declare const getListOfMinutes: (locale: string, valueAsString?: boolean) => {
    value: string | number;
    label: string;
}[];
export declare const getListOfSeconds: (locale: string, valueAsString?: boolean) => {
    value: string | number;
    label: string;
}[];
export declare const getLocalizedTimePartials: (locale: string, ampm?: 'auto' | boolean) => LocalizedTimePartials;
export declare const getSelectedHour: (date: Date | null, locale: string, ampm?: 'auto' | boolean) => number | "";
export declare const getSelectedMinutes: (date: Date | null) => number | "";
export declare const getSelectedSeconds: (date: Date | null) => number | "";
export declare const isAmPm: (locale: string) => boolean;
export declare const isValidTime: (time: string) => number | false;
