import Tag from '../Tag';
import SelfCloseTag from '../SelfCloseTag';
import { ParseOptions, TagName, TagOptions } from '../type';
declare class __Empty__ extends Tag {
    constructor(str: string, tagName: TagName | undefined, options: TagOptions);
    slim(content: string): string;
    parseValidSubTag(subTagStr: string, subTagName: string, options: ParseOptions): [string, any];
    parseOnlyString(subTagStr: string, subTagName: TagName, options: ParseOptions): [string, any];
    exec(): string;
}
declare class __EmptySelfClose__ extends SelfCloseTag {
    constructor(str: string, tagName?: string);
    exec(): string;
}
export { __Empty__, __EmptySelfClose__ };
