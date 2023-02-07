/* chew
   Copyright (C) 1990-1992 Free Software Foundation, Inc.
   Contributed by steve chamberlain @cygnus


This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.  */

/*
 Yet another way of extracting documentation from source.
 No, I haven't finished it yet, but I hope you people like it better
 that the old way
  
 sac

Basically, this is a sort of string forth, maybe we should call it
struth?

You define new words thus:
: <newword> <oldwords> ;
There is  no

*/



#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include <stdint.h>

#define DEF_SIZE 5000
#define STACK 50
#define MIN_CMDLEN	4	/* Minimum length of a command */

int internal_wanted;
int internal_mode;
int Verbose=0;



/* Here is a string type ... */

typedef struct buffer 
{
    char *ptr;
    unsigned int write_idx;
    unsigned int size;
} string_type;







static void
init_string_with_size (string_type *buffer, unsigned int size)
{
  buffer->write_idx = 0;
  buffer->size = size;
  buffer->ptr = malloc(size);
}

static void
init_string (string_type *buffer)
{
    init_string_with_size(buffer, DEF_SIZE);

}

static int
find (string_type *str, char *what)
{
    unsigned int i;
    char *p;
    p = what;
    for (i = 0; i < str->write_idx && *p; i++) 
    {
	if (*p == str->ptr[i])
	 p++;
	else
	 p = what;
    }
    return (*p == 0);
    
}

static void
write_buffer (string_type *buffer)
{
    fwrite(buffer->ptr, buffer->write_idx, 1, stdout);
}


static void
delete_string (string_type *buffer)
{
    free(buffer->ptr);
}


static char *
addr (string_type *buffer, unsigned int idx)
{
    return buffer->ptr + idx;
}

static char
at (string_type *buffer, unsigned int pos)
{
    if ( pos >= buffer->write_idx) 
    {
	return 0;
    }
    return buffer->ptr[pos];
}

static void
catchar (string_type *buffer, char ch)
{
  if (buffer->write_idx == buffer->size) 
  {
    buffer->size *=2;
    buffer->ptr = realloc(buffer->ptr, buffer->size);
    if (!buffer->ptr)
    {
      fprintf(stderr,"Can't allocate memory\n");
      exit(1);
    }
  }

  buffer->ptr[buffer->write_idx ++ ] = ch;
}


static void
overwrite_string (string_type *dst, string_type *src)
{
    free(dst->ptr);
    dst->size = src->size;
    dst->write_idx = src->write_idx;
    dst->ptr = src->ptr;
}

static void
catstr (string_type *dst, string_type *src)
{
    unsigned int i;
    for (i = 0; i < src->write_idx; i++) 
    {
	catchar(dst, src->ptr[i]);
    }
}


static void
cattext (string_type *buffer, char *string)
{
    
    while (*string) 
    {
	catchar(buffer, *string);
	string++;
    }
}

static void
catbuf (string_type *buffer, char *buf, unsigned int len)
{
    
    while (len--) 
    {
	catchar(buffer, *buf);
	buf++;
    }
}



static unsigned int 
skip_white_and_stars (string_type *src, unsigned int idx)
{
    while (isspace(at(src,idx)) 
	   || (at(src,idx) == '*' && at(src,idx +1) !='/')) 
     idx++;
    return idx;
    

}
/***********************************************************************/


string_type stack[STACK];
string_type *tos;

unsigned int idx = 0; /* Pos in input buffer */
string_type *ptr; /* and the buffer */
typedef void (*stinst_type)(void);
stinst_type *pc;
stinst_type sstack[STACK];
stinst_type *ssp = &sstack[0];
uintptr_t istack[STACK];
uintptr_t *isp = &istack[0];

typedef uintptr_t *word_type;



struct dict_struct
{
    char *word;
    struct dict_struct *next;
   stinst_type *code;
    int code_length;
    int code_end;
    int var;
    
};
typedef struct dict_struct dict_type;
#define WORD(x) static void x(void)

static void
exec (dict_type *word)
{
    pc = word->code;
    while (*pc) 
    {
	(*pc)();
    }
    
}
WORD(call)
{
stinst_type *oldpc = pc;
    dict_type *e;
    e =  (dict_type *)(pc [1]);
    exec(e);
    pc = oldpc + 2;
    
}

WORD(remchar)
{
    tos->write_idx--;    
    pc++;
    
}

WORD(push_number)
{
    isp++;
    pc++;
    *isp = (uintptr_t)(*pc);
    pc++;
    
}




WORD(push_text)
{
    
    tos++;
    init_string(tos);
    pc++;
    cattext(tos,*((char **)pc));
    pc++;
    
}


   
/* This function removes everything not inside comments starting on
   the first char of the line from the  string, also when copying
   comments, removes blank space and leading *'s 
   Blank lines are turned into one blank line
 */

static void 
remove_noncomments (string_type *src, string_type *dst)
{
    unsigned int idx = 0;
    
    while (at(src,idx)) 
    {
	/* Now see if we have a comment at the start of the line */
	if (at(src,idx) == '\n' 
	    && at(src,idx+1) ==  '/' 
	    && at(src,idx+2) == '*') 
	{
	    idx+=3;
	    
	    idx = skip_white_and_stars(src,idx);

	    /* Remove leading dot */
	    if (at(src, idx) == '.')
	     idx++;
	    
	    /* Copy to the end of the line, or till the end of the
	       comment */
	    while (at(src, idx))
	    {
		if (at(src, idx) == '\n') 
		{
		    /* end of line, echo and scrape of leading blanks  */
		    if (at(src,idx +1) == '\n')
		     catchar(dst,'\n');
		    catchar(dst,'\n');
		    idx++;
		    idx =   skip_white_and_stars(src, idx);
		}
		else if (at(src, idx) == '*' && at(src,idx+1) == '/') 
		{
		    idx +=2 ;
		    cattext(dst,"\nENDDD\n");
		    break;
		}
		else 
		{
		    catchar(dst, at(src, idx));
		    idx++;
		}
	    }
	}
	else idx++;
    }
}
/* turn foobar name(stuff); into foobar EXFUN(name,(stuff));

 */

static void
exfunstuff (void)
{
    unsigned int openp;
    unsigned int fname;
    unsigned int idx;
    string_type out;
    init_string(&out);
    

    /* make sure that it's not already exfuned */
    if(find(tos,"EXFUN") || find(tos,"PROTO") || !find(tos,"(")) {
	    catstr(&out,tos);
	}
    else 
    {
	
	/*Find the open paren*/
	for (openp = 0; at(tos, openp) != '('  && at(tos,openp); openp++)
	 ;

	fname = openp;
	/* Step back to the fname */
	fname--;
	while (fname && isspace(at(tos, fname)))
	 fname --;
	while (fname && !isspace(at(tos,fname)) && at(tos,fname) != '*')
	 fname--;

	fname++;
	
	for (idx = 0; idx < fname; idx++) 
	{
	    catchar(&out, at(tos,idx));
	}
    
	cattext(&out,"EXFUN(");
	for (idx = fname; idx < openp; idx++) 
	{
	    catchar(&out, at(tos,idx));
	}
	cattext(&out,", ");
	while (at(tos,idx) && at(tos,idx) !=';') 
	{
	    catchar(&out, at(tos, idx));
	    idx++;
	}
	cattext(&out,");\n");
    }
    overwrite_string(tos, &out);    
    pc++;
    
}



/* turn {*
   and *} into comments */

WORD(translatecomments)
{
    unsigned int idx = 0;
    string_type out;
    init_string(&out);
    
    while (at(tos, idx)) 
    {
	if (at(tos,idx) == '{' && at(tos,idx+1) =='*') 
	{
	    cattext(&out,"	/*");
	    idx+=2;
	}
	else if (at(tos,idx) == '*' && at(tos,idx+1) =='}') 
	{
	    cattext(&out,"*/");
	    idx+=2;
	}
	else  
	{
	    catchar(&out, at(tos, idx));
	    idx++;
	}
    }


    overwrite_string(tos, &out);
    
    pc++;
    
}

#if 0
/* turn everything not starting with a . into a comment */

WORD(manglecomments)
{
    unsigned int idx = 0;
    string_type out;
    init_string(&out);
    
    while (at(tos, idx)) 
    {
	if (at(tos,idx) == '\n' && at(tos,idx+1) =='*') 
	{
	    cattext(&out,"	/*");
	    idx+=2;
	}
	else if (at(tos,idx) == '*' && at(tos,idx+1) =='}') 
	{
	    cattext(&out,"*/");
	    idx+=2;
	}
	else  
	{
	    catchar(&out, at(tos, idx));
	    idx++;
	}
    }


    overwrite_string(tos, &out);
    
    pc++;
    
}
#endif

/* Mod tos so that only lines with leading dots remain */
static void
outputdots (void)
{
    unsigned int idx = 0;
    string_type out;
    init_string(&out);
    
    while (at(tos, idx)) 
    {
	if (at(tos, idx) == '\n' && at(tos, idx+1) == '.') 
	{
	    idx += 2;
	    
	    while (at(tos, idx) && at(tos, idx)!='\n')
	    {
		if (at(tos,idx) == '{' && at(tos,idx+1) =='*') 
		{
		    cattext(&out," /*");
		    idx+=2;
		}
		else if (at(tos,idx) == '*' && at(tos,idx+1) =='}') 
		{
		    cattext(&out,"*/");
		    idx+=2;
		}
		else  
		{
		    catchar(&out, at(tos, idx));
		    idx++;
		}
	    }
	    catchar(&out,'\n');
	}
	else 
	{
	    idx++;
	}
    }	

    overwrite_string(tos, &out);
    pc++;
    
}

/* Find lines starting with . and | and put example around them on tos
   turn 
   {*  into open comment and *} into close comment
   escape curlies
   
*/
WORD(courierize)
{
    string_type out;
    unsigned int idx = 0;
    
    init_string(&out);
    
    while (at(tos, idx)) 
    {
	if (at(tos, idx) == '\n' 
	    && (at(tos, idx +1 ) == '.'
		|| at(tos,idx+1) == '|')) 
	{
	    cattext(&out,"\n@smallexample\n");
	    do 
	    {
		idx += 2;
		
		while (at(tos, idx) && at(tos, idx)!='\n')
		{
		    if (at(tos,idx)=='{' && at(tos,idx+1) =='*') 
		    {
			cattext(&out," /*");
			idx+=2;
		    }
		    else if (at(tos,idx)=='*' && at(tos,idx+1) =='}') 
		    {
			cattext(&out,"*/");
			idx+=2;
		    }
	            else if (at(tos,idx) == '{')
		    {
			cattext(&out,"@{");
			idx++;
		    }
	            else if (at(tos,idx) == '}')
		    {
			cattext(&out,"@}");
			idx++;
		    }
		    else 
		    {
			catchar(&out, at(tos, idx));
			idx++;
		    }
		    
		}
		catchar(&out,'\n');
	    }  
	    while (at(tos, idx) == '\n' 
		   && (at(tos, idx+1) == '.')
		   || (at(tos,idx+1) == '|'));
	    cattext(&out,"@end smallexample");
	}
	else 
	{    
	    catchar(&out, at(tos, idx));
	    idx++;
	}
    }    

    overwrite_string(tos, &out);
    pc++;

    
}

/* 
bulletize:  look for bullet item commands at start of line
 Bullet list:
   O+  emit @itemize @bullet
   o   emit @item	[note lowercase]
   O-  emit @end itemize

 Variable label list:
   o+  emit @table @code
   o   emit @item
   o-  emit @end table
*/


WORD(bulletize)
{
  unsigned int idx = 0;
  string_type out;
  init_string(&out);
    
  while (at(tos, idx)) {
       if (at(tos, idx) == '\n' &&  at(tos, idx+1) == 'o')
       {
	 if (at(tos,idx+2) == '+') {
	     cattext(&out,"\n@table @code\n");
	     idx+=3;
	   }
	 else if (at(tos,idx+2) == '-') {
	     cattext(&out,"\n@end table\n");
	     idx+=3;
	   }
	 else if (isspace(at(tos,idx+2))) {
	     cattext(&out,"\n@item ");
	     idx+=3;
	   }
	 else {
	     catchar(&out, at(tos, idx));
	     idx++;
	   }
       }
      
       else
	if (at(tos, idx) == '\n' &&  at(tos, idx+1) == 'O')
	{
	  if (at(tos,idx+2) == '+') {
	      cattext(&out,"\n@itemize @bullet\n");
	      idx+=3;
	    }

	  else if (at(tos,idx+2) == '-') {
	      cattext(&out,"\n@end itemize\n");
	      idx+=3;
	    }
	  else {
	      catchar(&out, at(tos, idx));
	      idx++;
	    }
	}	      
	else
	{
	  catchar(&out, at(tos, idx));
	  idx++;
	}
    }

  delete_string(tos);
  *tos = out;
  pc++;
    
}

/* Turn <<foo>> into @code{foo} in place at TOS 
   Turn <[foo]> into @var{foo} in place at TOS
   nest them too !

*/
   

WORD(do_fancy_stuff)
 {
    unsigned int idx = 0;
    string_type out;
    init_string(&out);
    while (at(tos, idx)) 
    {
	if (at(tos, idx) == '<' 
	    && at(tos, idx+1) == '<'
	    && (!isspace(at(tos,idx + 2)) || at(tos,idx+3) == '>')) 
	{
	    /* This qualifies as a << startup */
	    idx +=2;
	    cattext(&out,"@code{");
	  }
	
	else 	if (at(tos, idx) == '<' 
	    && at(tos, idx+1) == '['
	    && !isspace(at(tos,idx + 2))) 
	{
	    /* This qualifies as a <[ startup */
	    idx +=2;
	    cattext(&out,"@var{");
	  }
	else if (at(tos, idx) == '>' 
		 && at(tos,idx+1) =='>') 
	{
	  
	    cattext(&out,"}");
	    idx+=2;
	}
	else if (at(tos, idx) == ']' 
		 && at(tos,idx+1) =='>') 
	{
	    cattext(&out,"}");
	    idx+=2;
	}
	else 
	{
	    catchar(&out, at(tos, idx));
	    idx++;
	}
    }
    delete_string(tos);
    *tos = out;
    pc++;
    
}
/* A command is all upper case,and alone on a line */
static int 
iscommand (string_type *ptr, unsigned int idx)
{
    unsigned int len = 0;

    while (isupper(at(ptr,idx)) || at(ptr,idx) == '_') {
	     len++;
	     idx++;
    }

    while (at(ptr,idx) == ' ') {
	     len++;
	     idx++;
    }

    if(at(ptr,idx) == '\n')
	    {
		/* The length check will never fail on a real command
		 * because the commands are screened as the definitions file
		 * is read.  */
		if (len >= MIN_CMDLEN) return 1;
		return 0;
	    }

    return 0;

}


unsigned int
copy_past_newline (string_type *ptr, unsigned int idx, string_type *dst)
{
    while (at(ptr, idx) && at(ptr, idx) != '\n') 
    {
	catchar(dst, at(ptr, idx));
	idx++;
	
    }    
    catchar(dst, at(ptr, idx));
    idx++;
    return idx;

}

WORD(icopy_past_newline)
{
    tos++;
    init_string(tos);
    idx = copy_past_newline(ptr, idx, tos);
    pc++;	
}


/* indent
   Take the string at the top of the stack, do some prettying */




WORD(kill_bogus_lines)
{
    int sl ;
    
    int idx = 0;
    int c;
    int dot = 0    ;
    
    string_type out;    
    init_string(&out);
    /* Drop leading nl */
    while (at(tos,idx) == '\n')
    {
	idx++;
    }
    c = idx;
    
    /* Find the last char */
    while (at(tos,idx))
    {
	idx++;
    }
    
    /* find the last non white before the nl */
    idx--;
    
    while (idx && isspace(at(tos,idx)))
     idx--;
    idx++;
    
    /* Copy buffer upto last char, but blank lines before and after
       dots don't count */
    sl = 1;

    while (c < idx)
    {
	if (at(tos,c) == '\n' 
	    && at(tos,c+1) == '\n'
	    && at(tos,c+2) == '.') 
	{
	    /* Ignore two linelines before  a dot*/
	    c++;
	}
	else if (at(tos,c) == '.' && sl)
	{
	    /* remember that this line started with a dot */
	    dot=2;
	}
	else if (at(tos,c) == '\n' 
		 && at(tos,c+1) == '\n'
		 && dot)
	{
	    c++;
	    /* Ignore two newlines when last line was dot */
	}

	catchar(&out, at(tos,c));
	if (at(tos,c) == '\n')
	{
	    sl = 1;
	    
	    if (dot == 2)dot=1;else dot = 0;
	}
	
	c++;	

    }
    
    /* Append nl*/
    catchar(&out, '\n');
    pc++;
    delete_string(tos);
    *tos = out;
    
    
}

WORD(indent)
{
    string_type out;
    int tab = 0;
    int idx = 0;
    int ol =0;
    init_string(&out);
    while (at(tos,idx)) {
	    switch (at(tos,idx)) 
	    {
	      case '\n':
		cattext(&out,"\n");
		idx++;
		if (tab) 
		{
		    cattext(&out,"    ");
		}
		ol = 0;
		break;
	      case '(':
		tab++;
		if (ol == 0)
		    cattext(&out,"   ");
		idx++;
		cattext(&out,"(");
		ol = 1;
		break;
	      case ')':
		tab--;
		cattext(&out,")");
		idx++;
		ol=1;
		
		break;
	      default:
		catchar(&out,at(tos,idx));
		ol=1;
		
		idx++;
		break;
	    }
	}	

    pc++;
    delete_string(tos);
    *tos = out;

}

/* Change the TOS so that all that is left is the stuff inside the
 first <<foo>> .
*/

WORD(get_stuff_in_angle)
{
  unsigned int idx = 0;
  string_type out;
  init_string(&out);
    
  while (at(tos, idx)) 
    {
      if (at(tos,idx) == '<' && at(tos,idx+1) =='<') 
	{
	  idx+=2;
	  
	  while (!(at(tos,idx) == '>' && at(tos,idx+1) == '>'))
	    {
	      catchar(&out, at(tos, idx));
	      idx++;
	    }
	  break;
	}
      idx++;
    }
  catchar(&out,'\n');
  
  overwrite_string(tos, &out);
  pc++;
}


WORD(get_stuff_in_command)
{
  tos++;
  init_string(tos);

  while (at(ptr, idx)) {
    if (iscommand(ptr, idx))  break;
    idx =   copy_past_newline(ptr, idx, tos);
  }
  pc++;    
}

WORD(swap)
{
    string_type t;
    
    t = tos[0];
    tos[0] = tos[-1];
    tos[-1] =t; 
    pc++;
    
}

WORD(dup_)
{
    tos++;
    init_string(tos);
    catstr(tos, tos-1);
    pc++;
    
}



WORD(icatstr)
{
    catstr(tos-1, tos);
    delete_string(tos);
    tos--;
    pc++;
    
}

WORD(skip_past_newline)
{
    while (at(ptr,idx) 
	   && at(ptr,idx) != '\n')
     idx++;
    idx++;
    pc++;
}


WORD(internalmode)
{
    internal_mode = *(isp);
    isp--;
    pc++;
}

WORD(maybecatstr)
{
    if (internal_wanted == internal_mode) 
    {
	catstr(tos-1, tos);
    }
    delete_string(tos);
    tos--;
    pc++;
    
}

/* write tos to stderr */
WORD(warn)
{
    fputs("Warning: ", stderr);
    fwrite(tos->ptr, tos->write_idx, 1, stderr);
    fputc('\n', stderr);
    delete_string(tos);
    tos--;
    pc++;
}

char *
nextword (char *string, char **word)
{
  char *word_start;
  int idx;
  char *dst;
  char *src;
    
  int length = 0;
    
  while (isspace(*string) || *string == '-') {
      if (*string == '-') 
      {
	while (*string && *string != '\n') 
	 string++;
		
      }
      else {
	  string++;
	}
    }
  if (!*string) return 0;
    
  word_start = string;    	
  if (*string == '"') 
  {
    string++;
    length++;
	
    while (*string != '"') 
    {
      string++;
      length++;
    }
  }
  else     
  {
	

    while (!isspace(*string)) 
    {
      string++;
      length++;
    }
  }
    
  *word = malloc(length + 1);

  dst = *word;
  src = word_start;


  for (idx= 0; idx < length; idx++) 
  {
    
    if (src[idx] == '\\' && src[idx+1] == 'n') 
    {
      *dst++ = '\n';
      idx++;
    
    }
    else *dst++ = src[idx];
  }
  *dst++ = 0;





  if(*string)    
   return string + 1;
  else 
   return 0;
    
}
dict_type *root;
dict_type *
lookup_word (char *word)
{
    dict_type *ptr = root;
    while (ptr) {
	    if (strcmp(ptr->word, word) == 0) return ptr;
	    ptr = ptr->next;
	    
	 }
    fprintf(stderr,"Can't find %s\n",word);
    return 0;
    
    
}

static int
perform (void)
{
    tos = stack;
    int errors = 0;
    
    while (at(ptr, idx)) {
	    /* It's worth looking through the command list */
	    if (iscommand(ptr, idx))
	    {
		char *next;
		dict_type *word ;
		
		(void)		nextword(addr(ptr, idx), &next);


		word = lookup_word(next);


		

		if (word) 
		{
		    if(Verbose)  fprintf(stderr, "CMD '%s'\n", word->word);
		    exec(word);
		}
		else
		{
		    fprintf(stderr,"warning, %s is not recognised\n",  next);
		    errors++;
		    skip_past_newline();
		}
		
	    }
	    else skip_past_newline();

	}
    return errors;
}

dict_type *
newentry (char *word)
{
    dict_type *new = (dict_type *)malloc(sizeof(dict_type));
    new->word = word;
    new->next = root;
    root = new;
    new->code = (stinst_type *)malloc(sizeof(stinst_type ));
    new->code_length = 1;
    new->code_end = 0;
    return new;
    
}


unsigned int
add_to_definition (dict_type *entry, stinst_type word)
{
    if (entry->code_end == entry->code_length) 
    {
	entry->code_length += 2;
	entry->code =
	 (stinst_type *) realloc((char *)(entry->code),
			       entry->code_length *sizeof(word_type));
    }
    entry->code[entry->code_end] = word;
    
return     entry->code_end++;  
}







void
add_intrinsic (char *name, void (*func)(void))
{
    dict_type *new = newentry(name);
    add_to_definition(new, func);
    add_to_definition(new, 0);
}

void
add_var (char *name)
{
    dict_type *new = newentry(name);
    add_to_definition(new, push_number);
    add_to_definition(new, (stinst_type)(&(new->var)));
    add_to_definition(new,0);
    
}
      



int
compile (char *string)
{
    int  ret=0;
    /* add words to the dictionary */
    char *word;
    dict_type *lookup;

    string = nextword(string, &word);
    while (string && *string && word[0]) 
    {
	if (strcmp(word,"var")==0) 
	{
	  string=nextword(string, &word);
	  
	  add_var(word);
	  string=nextword(string, &word);
	}
	else	
	    
	if (word[0] == ':')
	{
	    dict_type *ptr;
	    /* Compile a word and add to dictionary */
	    string = nextword(string, &word);
	    if(Verbose)  fprintf(stderr, "Found command '%s'\n", word);
	    if(strlen(word) < MIN_CMDLEN)  {
		fprintf(stderr, "ERROR:  Command '%s' is too short ", word);
		fprintf(stderr, "(MIN_CMDLEN is %d)\n", MIN_CMDLEN);
		ret++;
	    }
	    
	    ptr = newentry(word);
	    string = nextword(string, &word);
	    while (word[0] != ';' ) 
	    {
		 switch (word[0]) 
		 {
		    
		    
		   case '"':
		     /* got a string, embed magic push string
			function */
		     add_to_definition(ptr, push_text);
		     add_to_definition(ptr, (stinst_type)(word+1));
		     break;
		   case '0':
		   case '1':
		   case '2':
		   case '3':
		   case '4':
		   case '5':
		   case '6':
		   case '7':
		   case '8':
		   case '9':
		     /* Got a number, embedd the magic push number
			function */
		     add_to_definition(ptr, push_number);
		     add_to_definition(ptr, (stinst_type)atol(word));
		     break;
		   default:
		     add_to_definition(ptr, call);
		     lookup = lookup_word(word);
		     if (!lookup) ret++;
		     add_to_definition(ptr, (stinst_type)lookup);
		 }

		string = nextword(string, &word);		     
	    }
	    add_to_definition(ptr,0);
	    string = nextword(string, &word);
	}
	else 
	{
	    fprintf(stderr,"syntax error at %s\n",string-1);
	    ret++;
	}	    
    }

    free(word);
    return(ret);
}

 
static void
bang (void)
{
*(uintptr_t *)((isp[0])) = isp[-1];
isp-=2;
pc++;

}

WORD(atsign)
{
    isp[0] = *(uintptr_t *)(isp[0]);
    pc++;
}

WORD(hello)
{
    
    printf("hello\n");
    pc++;    
}



static void
read_in (string_type *str, FILE *file)
{
    char buff[10000];    
    unsigned int r;
    do 
    {
	r = fread(buff, 1, sizeof(buff), file);
	catbuf(str, buff, r);
    }
    while (r);
    buff[0] = 0;
    
    catbuf(str, buff,1);
    
}


#if 0
static void
usage (void)
{
    fprintf(stderr,"usage: -[i|v] -f macrofile <file >file\n");
    exit(33);    
}
#endif

int
main (int ac, char *av[])
{
    unsigned int i;
    int status = 0;

    string_type buffer;
    string_type pptr;
    

    init_string(&buffer);
    init_string(&pptr);
    init_string(stack+0);
    tos=stack+1;
    ptr = &pptr;
    
    add_intrinsic("push_text", push_text);
    add_intrinsic("!", bang);
    add_intrinsic("@", atsign);
    add_intrinsic("hello",hello);    
    add_intrinsic("skip_past_newline", skip_past_newline );
    add_intrinsic("catstr", icatstr );
    add_intrinsic("copy_past_newline", icopy_past_newline );
    add_intrinsic("dup", dup_ );
    add_intrinsic("remchar", remchar );
    add_intrinsic("get_stuff_in_command", get_stuff_in_command );
    add_intrinsic("get_stuff_in_angle", get_stuff_in_angle );
    add_intrinsic("do_fancy_stuff", do_fancy_stuff );
    add_intrinsic("bulletize", bulletize );
    add_intrinsic("courierize", courierize );
    add_intrinsic("swap", swap );
    add_intrinsic("outputdots", outputdots );
    add_intrinsic("exfunstuff", exfunstuff );
    add_intrinsic("maybecatstr", maybecatstr );
    add_intrinsic("translatecomments", translatecomments );
    add_intrinsic("kill_bogus_lines", kill_bogus_lines);
    add_intrinsic("indent", indent);
    add_intrinsic("internalmode", internalmode);
    add_intrinsic("warn", warn);

    /* Put a nl at the start */
    catchar(&buffer,'\n');

    read_in(&buffer, stdin); 
    remove_noncomments(&buffer, ptr);
    for (i= 1; i < ac; i++) 
    {
	if (av[i][0] == '-')
	{
	    if (av[i][1] == 'f')
	    {
		string_type b;
		FILE *f;
		init_string(&b);

		f  = fopen(av[i+1],"r");
		if (!f) 
		{
		  fprintf(stderr,"Can't open the input file %s\n",av[i+1]);
		  return 33;
		}
		if(Verbose)  fprintf(stderr, "Reading -f '%s'\n", av[i+1]);
		
		  
		read_in(&b, f);
		if( compile(b.ptr) )  { fclose(f); exit(1); }
		status = perform();
		fclose(f);
	    }
	    else    if (av[i][1] == 'i') 
	    {
		internal_wanted = 1;
	    }
	    else    if (av[i][1] == 'v') 
	    {
		Verbose++;
	    }
	}

    }      
    write_buffer(stack+0);
    return status;
}
