import { ParseOptions, TagName } from '../type';
declare class __RawString__ {
    tagName: TagName;
    nextTagName: TagName;
    prevTagName: TagName;
    prevTagStr: string;
    hasEndSpace: boolean;
    hasStartSpace: boolean;
    prevHasStartSpace: boolean;
    prevHasEndSpace: boolean;
    parentTag: TagName;
    keepSpace: boolean;
    calcLeading: boolean;
    inTable: boolean;
    leadingSpace: string;
    layer: number;
    rawStr: string;
    constructor(str: string, tagName?: TagName, { keepSpace, prevTagName, nextTagName, prevTagStr, prevHasEndSpace, prevHasStartSpace, parentTag, calcLeading, layer, leadingSpace, inTable, }?: ParseOptions);
    slim(str: string): string;
    beforeReturn(content: string): string;
    exec(): string;
}
export default __RawString__;
