#ifndef _MBCTYPE_H_

#define _MBCTYPE_H_

/* escape character used for JIS encoding */
#define ESC_CHAR 0x1b

/* functions used to support SHIFT_JIS, EUC-JP, and JIS multibyte encodings */

int _issjis1 (int c);
int _issjis2 (int c);
int _iseucjp (int c);
int _isjis (int c);

#define _issjis1(c)    (((c) >= 0x81 && (c) <= 0x9f) || ((c) >= 0xe0 && (c) <= 0xef))
#define _issjis2(c)    (((c) >= 0x40 && (c) <= 0x7e) || ((c) >= 0x80 && (c) <= 0xfc))
#define _iseucjp1(c)   ((c) == 0x8e || (c) == 0x8f || ((c) >= 0xa1 && (c) <= 0xfe))
#define _iseucjp2(c)   ((c) >= 0xa1 && (c) <= 0xfe)
#define _isjis(c)      ((c) >= 0x21 && (c) <= 0x7e)

#endif /* _MBCTYPE_H_ */
