* Copyright IBM Corp. and others 2016
      ACONTROL AFPR,FLAG(CONT)

FFISYS CELQPRLG DSASIZE=DSASZ,PSECT=ASP

*FFISYS ARGS:
*r1 <- foreign_function_address (2176) (+0)
*r2 <- &ecif (2116) (+8)
*r3 <- cif->flags (2120) (+20)
*@2124(,4) <- ecif->rvalue (+24)?
*@2128(,4) <- cif->bytes (+36)?
*@2132(,4) <- cif->nargs (+44)?
*@2136(,4) <- cif->arg_types->size (+52)?

         USING  CEEDSAHP,4

*Store argument registers on the stack
         STG 1,(2176+(((DSASZ+31)/32)*32))(,4)
         STG 2,(2176+(((DSASZ+31)/32)*32)+8)(,4)
         STG 3,(2176+(((DSASZ+31)/32)*32)+16)(,4)

         LG 14,0(,2)           ecif->cif
         LG 14,8(,14)          cif->arg_types
*What: Storing arguments in this routine's
*      local storage for future use
*Name:    ffi_prep_args_call
*Input:   stack, extended_cif
*Output:  void
*Action:  Is an external call to C-XPLINK routine
*         It saves function's arguments in this 
*         routine's local storage
         LA 1,LSTOR          
         LGR 13,1 
         CELQCALL   PREPARGS,WORKREG=10

         LGR 5,14              Copy of parameter types
*Reset registers used in code gen
*         SR  0,0              GPR counter
          LA  0,0
*         SR  14,14            FPR counter
          LA  14,0
*         SR  7,7              Offset in the arg area
          LA  7,0
*         SR  10,10            Offset in array of parm types
          LA  10,0
*         SR  6,6              Offset in stored parm values
          LA  6,0

*Dumb handling for now, but if struct return with size > 24
*bytes, we need to allocate space for the dummy argument
*that holds the return value pointer 
         LG 15,(2176+(((DSASZ+31)/32)*32)+8)(,4)
         LG 15,0(,15)           ecif->cif
         LG 15,16(,15)          cif->rtype
         LG 15,0(,15)           rtype->size
         CGIJNH 15,24,GETNARGS

         LG 1,(2176+(((DSASZ+31)/32)*32)+24)(,4)         
         AHI 0,1                One less gpr to work with
         AHI 7,8                argument area is 8 bytes larger

GETNARGS DS 0H
*Get the cif->nargs from caller's stack
         L   9,(2176+(((DSASZ+31)/32)*32)+44)(,4) 
         CIJE 9,0,CALL

*Place arguments passed to the foreign function based on type
ARGLOOP  LG  11,0(10,5)       Get pointer to current ffi_type
         LLGC 11,11(11)       ffi_type->type
         SLL 11,2             Find offset in branch tabel
         LA  15,ATABLE        
         L   15,0(11,15)      
         BR  15
 
*Following code prepares ffi arguments, according to xplink

* technically, this isn't allowed 
* but openJ9 uses ffi_type_void for void functions
* so support it since it doesn't break anything
* assuming we don't have something weird like a void type
* followed by real parameters
VOID     DS  0H               ffi_type_void
         B CALL

I        DS  0H               ffi_type_int
UI32     DS 0H                ffi_type_uint32
         LA 15,I32
         LR 11,0
         SLL 11,2             Pass this parm in gpr or arg area
         L  15,0(11,15)
         CFI  0,3             GPRs left to pass parms in?
         BL INC
         LA 0,3               Reached max gprs
         B  J
INC      DS 0H
         AHI 0,1              Now we have one less gpr left
J        DS 0H
         BR 15

IGPR1    DS 0H                INT/UI32 type passed in gpr1
         L 1,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,4              Advance to next word in parm value
         B CONT               Next parameter
IGPR2    DS 0H                INT/UI32 type passed in gpr2
         L 2,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,4              Advance to next word in parm value
         B CONT               Next parameter
IGPR3    DS 0H                INT/UI32 type passed in gpr3
         L 3,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,4              Advance to next word in parm value
         B CONT               Next parameter
IARGA    DS 0H                INT/UI32 stored in arg area
         L 11,0(6,13)         Argument value
         LA 15,2176(,4)       Start of arg area
         STG 11,0(7,15)        Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,4              Advance to next word in parm value
         B CONT               Next parameter

UI8      DS 0H                ffi_type_uint8
SI8      DS 0H                ffi_type_sint8 
         LA 15,I8
         LR 11,0
         SLL 11,2             Pass this parm in gpr or arg area
         L  15,0(11,15)
         CFI  0,3             GPRs left to pass parms in?
         BL INC2
         LA 0,3               Reached max gprs
         B  J2
INC2     DS 0H
         AHI 0,1              Now we have one less gpr left
J2       DS 0H
         BR 15 

I8GPR1   DS 0H                Char type passed in gpr1
         LLC 1,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,1              Advance the first byte of parm value
         B  CONT              Next parameter
I8GPR2   DS 0H                Char type passed in gpr2
         LLC 2,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,1              Advance the first byte of parm value
         B CONT               Next parameter
I8GPR3   DS 0H                Char type passed in gpr3
         LLC 3,0(6,13)   
         AHI 7,8              Advance to the next word in arg area
         AHI 6,1              Advance the first byte of parm value
         B CONT
I8ARGA   DS 0H                Char stored in arg area
         LLC 11,0(6,13)       Argument value
         LA 15,2176(,4)       Start of arg area
         STG 11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,1              Advance the first byte of parm value
         B CONT               Next parameter

UI16     DS 0H                ffi_type_uint16
         LA 15,U16
         LR 11,0
         SLL 11,2
         L  15,0(11,15)       Pass this parm in gpr or arg area
         CFI  0,3             GPRs left to pass parms in?
         BL INC3
         LA 0,3               Reached max gprs
         B  J3
INC3     DS 0H
         AHI 0,1              Now we have one less gpr left
J3       DS 0H
         BR 15 

U16GPR1  DS 0H                u_short type passed in gpr1
         LLH 1,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
U16GPR2  DS 0H                u_short type passed in gpr2
         LLH 2,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
U16GPR3  DS 0H                u_short passed in gpr3
         LLH 3,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
U16ARGA  DS 0H                u_short in arg area
         LLH 11,0(6,13)       Argument value
         LA 15,2176(,4)       Start of arg area
         STG 11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter

SI16     DS 0H                ffi_type_sint16
         LA 15,S16
         LR 11,0
         SLL 11,2            Pass this parm in gpr or arg area
         L  15,0(11,15)      
         CFI  0,3             GPRs left to pass parms in?
         BL INC4
         LA 0,3               Reached max gprs
         B  J4            
INC4     DS 0H
         AHI 0,1              Now we have one less gpr left
J4       DS 0H
         BR 15 

S16GPR1  DS 0H                s_SHORT type passsed in gpr1
         LH 1,0(6,13)   
         AHI 7,8              Advance to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
S16GPR2  DS 0H                s_SHORT type passed in gpr2
         LH 2,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
S16GPR3  DS 0H                s_SHORT type passed in gpr3
         LH 3,0(6,13)
         AHI 7,8              Advance to next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter
S16ARGA  DS 0H                s_SHORT in arg area
         LH 11,0(6,13)        Argument value
         LA 15,2176(,4)       Start of arg area
         STG 11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,2              Advance the first 2 bytes of parm value
         B CONT               Next parameter

SI64     DS 0H                ffi_type_sint64
         LA 15,S64
         LR 11,0
         SLL 11,2             Pass this parm in gpr or arg area
         L  15,0(11,15)
         CFI  0,3             GPRs left to pass parms in?
         BL INC5
         LA 0,3               Reached max gprs
         B  J5
INC5     DS 0H
         AHI 0,1              Now we have two less gpr left
J5       DS 0H
         BR 15 

S64GPR1 DS 0H                INT64 type passed in gpr1
         LG  1,0(6,13)
         AHI 7,8              Advance next two words in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
S64GPR2 DS 0H                INT64 type passed in gpr2,gpr3
         LG  2,0(6,13)
         AHI 7,8              Advance next two words in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
S64GPR3  DS 0H                INT64 type passed in gpr2
         LG  3,0(6,13)
         AHI 7,8              Advance next two words in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
S64ARGA  DS 0H                INT64 in arg area
         LG  11,0(6,13)        Argument value
         LA 15,2176(,4)       Start of arg area
         STG  11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump one word in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter

PTR      DS 0H                ffi_type_pointer
         LA 15,PTRS
         LR 11,0
         SLL 11,2             Pass this parm in gpr or arg area
         L  15,0(11,15)      
         CFI  0,3             GPRs left to pass parms in?
         BL INC6
         LA 0,3               Reached max gprs
         B  J6
INC6     DS 0H
         AHI 0,1              Now we have one less gpr left
J6       DS 0H
         BR 15 

PTRG1    DS 0H                PTR type passed in gpr1
         LG 1,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,8
         B CONT               Next parameter
PTRG2    DS 0H                PTR type passed in gpr2
         LG 2,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,8
         B CONT               Next parameter
PTRG3    DS 0H                PTR type passed in gpr3
         LG 3,0(6,13)
         AHI 7,8              Advance to the next word in arg area
         AHI 6,8
         B CONT               Next parameter
PTRARG   DS 0H                PTR in arg area
         LG 11,0(6,13)         Argument value
         LA 15,2176(,4)       Start of arg area
         STG 11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,8
         B CONT               Next parameter

UI64     DS 0H                ffi_type_uint64
         LA 15,UI64S
         LR 11,0
         SLL 11,2             Pass this parm in gpr or arg area
         L 15,0(11,15)
         CFI 0,2              GPRs left to pass parms in?
         BL INC64
         LA 0,3               Reached max gprs
         B J64
INC64    DS 0H
         AHI 0,1
J64      DS 0H
         BR 15

U64GP1   DS 0H                u_INT64 passed in gpr1, gpr2
         LG 1,0(6,13)  
         AHI 7,8              Advance two slots in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
U64GP2   DS 0H                u_INT64 passed in gpr2, gpr3
         LG 2,0(6,13) 
         AHI 7,8              Advance two slots in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
U64GP3   DS 0H                u_INT64 passed in gpr2
         LG 3,0(6,13)
         AHI 7,8              Advance next word in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
U64ARGA  DS 0H                u_INT64 in arg area
         LG 11,0(6,13)      Argument value
         LA 15,2176(,4)       Start of arg area
         STG  11,0(7,15)       Store in next two words in arg area
         AHI 7,8              Bump one word in arg area
         AHI 6,8              Advance the first 8 bytes of parm value
         B CONT               Next parameter
   
FLT      DS 0H                ffi_type_float
         LA 15,FLTS
         LR 11,14
         SLL 11,2             Pass in fpr or arg area
         L 15,0(11,15)
         CFI 14,4             FPRs left to pass parms in?            
         BL INC7L
         LA 14,4              Reached max fprs
         B JL7
INC7L    DS 0H
         AHI 14,1             Now we have one less fpr left
         CFI 0,3
         BL INCGF
         LA 0,3
         B JL7
INCGF    DS 0H
         AHI 0,1
JL7      DS 0H
         BR 15

FLTR0    DS 0H                FLOAT passed in fpr0
         LE 0,0(6,13)
         LER 11,0
         B FLTSTR
FLTR2    DS 0H                FLOAT passed in fpr2
         LE 2,0(6,13)
         LER 11,2
         B FLTSTR
FLTR4    DS 0H                FLOAT passed in fpr4
         LE 4,0(6,13)
         LER 11,4
         B FLTSTR
FLTR6    DS 0H                FLOAT passed in fpr6
         LE 6,0(6,13)
         LER 11,6
         B FLTSTR
ARGAFT   DS 0H                FLOAT in arg area
         LE 11,0(6,13)        Argument value
FLTSTR   DS 0H
         LA 15,2176(,4)       Start of arg area
         STE 11,0(7,15)       Store in next word in arg area
         AHI 7,8              Bump to the next word in arg area
         AHI 6,4              Advance the first 4 bytes of parm value
         B CONT               Next parameter

D        DS 0H                ffi_type_double
         LA 15,FLD
         LR 11,14
         SLL 11,2             Pass in fpr or arg area
         L  15,0(11,15)
         CFI  14,4            FPRs left to pass parms in?
         BL INC7
         LA 14,4              Reached max fprs
         B  J7
INC7     DS 0H
         AHI 14,1             Now we have one less fpr left
         CFI 0,2              Reached max gprs
         BL INCGD
         LA 0,3
         B J7
INCGD    DS 0H
         AHI 0,1
J7       DS 0H
         BR 15 

FLDR0    DS 0H                DOUBLE passed in fpr0
         LD 0,0(6,13)
         LDR 11,0
         B DBLSTR
FLDR2    DS 0H                DOUBLE passed in fpr2
         LD 2,0(6,13)
         LDR 11,2
         B DBLSTR
FLDR4    DS 0H                DOUBLE passed in fpr4
         LD 4,0(6,13)
         LDR 11,4
         B DBLSTR
FLDR6    DS 0H                DOUBLED passed in fpr6
         LD 6,0(6,13)
         LDR 11,6
         B DBLSTR
ARGAFL   DS 0H                DOUBLE in arg area
         LD 11,0(6,13)        Argument value
DBLSTR   DS 0H
         LA 15,2176(,4)       Start of arg area
         STD 11,0(7,15)       Store in next two words in arg area
         AHI 7,8              Bump to the next two words in arg area
         AHI 6,8              Bump stack twice, cuz double is 8byte
         B CONT               Next parameter

LD       DS 0H                ffi_type_longdouble
         LA 15,LDD
         SR  11,11
         CFI 14,0             All linkage fprs are available
         BE  0(11,15)         Pass l_DOUBLE in fpr0-fpr2
         LA  11,8
         CFI 14,4
         BH  0(11,15)         Pass l_DOUBLE in arg area
         LA 11,4
         L  15,0(11,15)       Pass l_DOUBLE in fpr4-fpr6
         BR 15 

DFPR0    DS 0H                l_DOUBLE passed in fpr0-fpr2
         LD 0,0(6,13)
         LA 15,2176(,4)       Start of arg area
         STD 0,0(7,15)       Store the first 8bytes in arg area
         AHI 6,8              Bump stack to next parameter
         LD 2,0(6,13)         l_DOUBLE passed in fpr0-fpr2
         STD 2,8(7,15)       Store the second 8bytes in arg area
         AHI 6,4              Bump stack once here, once at end
         AHI 7,16             Advance two slots 
         AHI 14,2             Now we have two less fprs left
         B CONT               Next Parameter
DFPR4    DS 0H                l_DOUBLE passed in fpr4-fpr6
         LD 4,0(6,13)     
         LA 15,2176(,4)       Start of arg area
         STD 4,0(7,15)       Store the first 8bytes in arg area
         AHI 6,8              Bump stack to next parameter
         LD 6,0(6,13)         l_DOUBLE passed in fpr4-fpr6
         STD 6,8(7,15)       Store the second 8bytes in arg area
         AHI 6,4              Bump stack once here, once at end
         AHI 7,16             Advance two slots
         AHI 14,2             Now we have two less fprs left
         B CONT               Next parameter
DARGF    DS 0H                l_DOUBLE in arg area
         LD 11,0(6,13)        Argument value
         LA 15,2176(,4)       Start of arg area
         STD 11,0(7,15)       Store the first 8bytes in arg area
         AHI 6,8              Bump stack to next parameter
         LD 11,0(6,13)        Argument value next 8bytes
         STD 11,8(7,15)       Store the second 8bytes in arg area
         AHI 7,16             Advance two slots
         LA  14,4             We reached max fprs
         B CONT               Next parameter

*If we have spare gprs, pass up to 24 bytes in GPRs. 
STRCT    DS 0H
         LG  11,0(10,5)
         LG 15,0(,11)          type->size
*todo NULL check?

*check if first element is float or double 
STFPCHK  DS 0H  
         LG 15,16(,11)         type->elements
         LG 15,0(,15)           type->elements[0]
         LH 15,10(,15)          type->elements[0]->type
         CFI 15,11               is it a float?
         BE STFPCHKF
         CFI 15,1               is it a double?
         BE STFPCHKD
         B STRCT2

*first arg is a float
STFPCHKF DS 0H
         LG 15,16(,11)          type->elements
         LA 15,8(,15)           type->elements[0]
         LG 15,0(,15)
         LH 15,10(,15)          type->elements[0]->type
         CFI 15,11               is it a float?
         BE STFPCHKF2
         B STRCT2

*first arg is a double
STFPCHKD DS 0H
         LG 15,16(,11)          type->elements
         LA 15,8(,15)           type->elements[1]
         LG 15,0(,15)
         LH 15,10(,15)          type->elements[1]->type
         CFI 15,1               is it a double?
         BE STFPCHKD2
         B STRCT2


*check if there are more elements
*if not we have a special case
*I think this is to handle complex types
*in this case we pass the struct
*in the first 2 free FPRs, just check this
*against r14 the free FPR counter
STFPCHKF2 DS 0H
         LG 15,16(,11)          type->elements
         LA 15,16(,15)           type->elements[0]
         LG 15,0(,15)
         CFI 15,0
         BNE STRCT2             if no, not special case

         CFI 14,4               no FPRs are available
         BNL STRCT2             if yes, not special case

         CFI 14,3               1 FPR is available                
         BNL STRCT2             if yes, struct won't fit

         CFI 14,2
         BE STFPCHKF246

         CFI 14,1
         BE STFPCHKF224

         CFI 14,0
         BE STFPCHKF202

STFPCHKF202 DS 0H
         LE 0,0(6,13)           first float
         LE 2,4(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,8
         AFI 15,-16          If struct is <24 bytes arg area
         AFI 7,8            Needs padding to 24 bytes

         B STRCTLP

STFPCHKF224 DS 0H
         LE 2,0(6,13)           first float
         LE 4,4(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,8
         AFI 15,-8          If struct is <24 bytes arg area
         AFI 7,8            Needs padding to 24 bytes

         B STRCTLP


STFPCHKF246 DS 0H
         LE 4,0(6,13)           first float
         LE 6,4(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,8
         AFI 15,-8              If struct is <24 bytes arg area
         AFI 7,8                Needs padding to 24 bytes

         B STRCTLP



*check if there are more elements
*if not we have a special case
*I think this is to handle complex types
*in this case we pass the struct
*in the first 2 free FPRs, just check this
*against r14 the free FPR counter
STFPCHKD2 DS 0H
         LG 15,16(,11)          type->elements
         LA 15,16(,15)           type->elements[0]
         LG 15,0(,15)
         CFI 15,0
         BNE STRCT2             if no, not special case

         CFI 14,4               no FPRs are available
         BNL STRCT2             if yes, not special case

         CFI 14,3               1 FPR is available                
         BNL STRCT2             if yes, struct won't fit

         CFI 14,2
         BE STFPCHKD246

         CFI 14,1
         BE STFPCHKD224

         CFI 14,0
         BE STFPCHKD202


STFPCHKD202 DS 0H
         LD 0,0(6,13)           first float
         LD 2,8(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,16
         AFI 15,-16          If struct is <24 bytes arg area
         AFI 7,16            Needs padding to 24 bytes

         B STRCTLP

STFPCHKD224 DS 0H
         LD 2,0(6,13)           first float
         LD 4,8(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,16
         AFI 15,-16          If struct is <24 bytes arg area
         AFI 7,16            Needs padding to 24 bytes

         B STRCTLP


STFPCHKD246 DS 0H
         LD 4,0(6,13)           first float
         LD 6,8(6,13)           second float
         AFI 0,2                one less GPR available
         AFI 14,2               two less FPRs available

         AFI 6,16
         AFI 15,-16          If struct is <24 bytes arg area
         AFI 7,16            Needs padding to 24 bytes

         B STRCTLP


*determine how to pass the struct based on size
*at this point we've weeded out all the float/double
*pair structs that get passed purely in FPRs
STRCT2  DS 0H
         LG 15,0(,11)          type->size         
         CFI 15,8              Struct <= 8 bytes?
         BNH  BYTE8
         CFI 15,16             Struct <= 16 bytes?
         BNH   BYTE16
         CFI 15,24             Struct <= 24 bytes?
         B BYTE24

BYTE8    DS 0H               Struct <= 8 bytes

*Since a struct here can be <8 bytes
*we need to pad it to 8 bytes in the arg area
*since saves in the arg area always assume 8 bytes for register
*so even on a for example 1 byte struct, the arg area has 8 bytes
*this is true for all cases where
*max struct size < register storage used
*so <8 byte sturcts regardless of register storage used, will be padded
*similarly with <16 byte structs using 2 registers,
*and <24 byte structs
*using all 3 registers
*I assume this is because the first 24 bytes of the arg area are
*technically the save area for the first 3 registers
BYTE8R1  DS 0H               Struct goes in R1
         CFI 0,1             is R1 available?
         BNL BYTE8R2

         LG 1,0(6,13)

         AGR 6,15            Advance to next byte in arg area
         AFI 15,-8           If struct is <8 bytes arg area
         AFI 7,8             Needs padding to 8 bytes

         AFI 0,1
         B STRCTLP

BYTE8R2  DS 0H               Struct goes in R2
         CFI 0,2             is R2 available?
         BH BYTE8R3

         LG 2,0(6,13)

         AGR 6,15           Advance to next byte in arg area
         AFI 15,-8          If struct is <8 bytes arg area
         AFI 7,8            Needs padding to 8 bytes

         AFI 0,1
         B STRCTLP


BYTE8R3  DS 0H               Struct goes in R3
         CFI 0,3             is R3 available?
         BNL STRCTLP

         LG 3,0(6,13)

         AGR 6,15           Advance to next byte in arg area
         AFI 15,-8          If struct is <8 bytes arg area
         AFI 7,8            Needs padding to 8 bytes

         AFI 0,1
         B STRCTLP

BYTE8F0  DS 0H               Struct goes in FPR0
BYTE8F2  DS 0H               Struct goes in FPR2
BYTE8F4  DS 0H               Struct goes in FPR4
BYTE8F6  DS 0H               Struct goes in FPR6

BYTE16   DS 0H               Struct <= 16 bytes

BYTE16R1 DS 0H               Struct goes in R1-R2
         CFI 0,1             are R1+R2 available?
         BNL BYTE16R2
        
         LG 1,0(6,13)
         LG 2,8(6,13)

         AGR 6,15            Advance to next byte in arg area
         AFI 15,-16          If struct is <16 bytes arg area
         AFI 7,16            Needs padding to 16 bytes

         AFI 0,2
         B STRCTLP


BYTE16R2 DS 0H               Struct goes in R2-R3
         CFI 0,2             are R2+R3 available?
         BNL BYTE16R3
         
         LG 2,0(6,13)
         LG 3,8(6,13)

         AGR 6,15            Advance to next byte in arg area
         AFI 15,-16          If struct is <16 bytes arg area
         AFI 7,16            Needs padding to 16 bytes

         AFI 0,2
         B STRCTLP
         

BYTE16R3 DS 0H               Struct goes in R3+Memory
         CFI 0,3             are R3 available?
         BNL STRCTLP
         LG 3,0(6,13)

         AFI 0,2
         B STRCTLP

BYTE16F0 DS 0H               Struct goes in FPR0-FPR2
BYTE16F2 DS 0H               Struct goes in FPR2-FPR4
BYTE16F4 DS 0H               Struct goes in FPR4-FPR6


BYTE24   DS 0H               Struct <= 24 bytes


BYTE24R1 DS 0H               Struct goes in R1-R3
         CFI 0,1             are R1+R2+R3 available?
         BNL BYTE24R2 
         LG 1,0(6,13)
         LG 2,8(6,13)
         LG 3,16(6,13)

         AGR 6,15            Advance to next byte in arg area
         AFI 15,-24          If struct is <24 bytes arg area
         AFI 7,24            Needs padding to 24 bytes

         AFI 0,3
         B STRCTLP

BYTE24R2 DS 0H               Struct goes in R2,R3+(potentially)Memory
         CFI 0,2             are R1+R2+R3 available?
         BNL BYTE24R3 
         LG 2,0(6,13)
         LG 3,8(6,13)
        
         AFI 0,3
         B STRCTLP

BYTE24R3 DS 0H               Struct goes in R3+Memory
         CFI 0,3             are R3 available?
         BNL STRCTLP 
         LG 3,0(6,13)

         AFI 0,3
         B STRCTLP

BYTE24F0 DS 0H               Struct goes in FPR0-FPR4+Memory
BYTE24F2 DS 0H               Struct goes in FPR2-FPR6+Memory
BYTE24F4 DS 0H               Struct goes in FPR4-FPR6+Memory
BYTE24F6 DS 0H               Struct goes in FPR6+Memory
 
STRCTLP  DS 0H               Rest of struct goes in Memory
         CFI 15,0            Size remaining > 0?
         BL CONT

         LB 12,0(6,13)        Load the byte of the struct
         STC 12,2176(7,4)     Store in next byte in arg area

         AFI  6,1            Move to next byte in struct
         AFI  7,1            Move to next byte in arg area
         AFI 15,-1           Decrement size of struct
         B  STRCTLP


CONT     DS 0H                End of processing curr_param
         AHI 10,8             Next parameter type
*        AHI 6,4              Next parameter value stored 
         BCT 9,ARGLOOP        
  
*Get function address, first argument passed,
*and return type, third argument passed from caller's
*argument area.
CALL     DS 0H
*         SR 11,11
         LA 11,0
         LG 6,(2176+(((DSASZ+31)/32)*32))(,4)
         L 11,(2176+(((DSASZ+31)/32)*32)+20)(,4)
  
*Call the foreign function using its address given 
*to us from an xplink compiled routine

*         L 5,16(,6)
*         L 6,20(,6)
         LMG 5,6,0(6)
         BASR 7,6
         DC    X'0700'
 
*What: Processing the return value based
*      on information in cif->flags, 3rd
*      parameter passed to this routine

         LA 15,RTABLE
         SLL 11,2             Return type
         L  15,0(11,15)
         BR 15

RF       DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         STE 0,0(,7)
         B RET

RD       DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         STD 0,0(,7)
         B RET

RLD      DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         STD 0,0(,7)
         STD 2,8(,7)
         B RET

RI       DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         ST 3,0(,7)
         B RET

RLL      DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         STG 3,0(7)
         B RET

RV       DS 0H
         B RET

RS       DS 0H
         LG 7,(2176+(((DSASZ+31)/32)*32)+24)(,4)
         LG 14,(2176+(((DSASZ+31)/32)*32)+8)(,4)
         LG 14,0(,14)           ecif->cif
         LG 9,16(,14)           cif->rtype
         LG 14,0(,9)            rtype->size
         CGIBH 14,24,RSP

* now we need to determine how to return the struct
* this label determines if the struct is <= 24 bytes
* if it is we return using gprs/frprs
* we then loop over rtype->elements
* to determine whether this struct is all floating point
* or if it is contains integral types
* if we have just floating point types use FPRs as appropriate
* but only if we have just the same type of float
* a struct mixing float, double and long double will use GPRs
* i have no idea why it is done this way, but it is
* also if we use more than 2 floating point types we use GPRs
* if we have at least one integral type, we use GPRs based on size
* if the struct is > 24 bytes we have already passed in the return
* pointer as the first argument to the callee "fn" 
* so that work was outsource to the compiler
* turning this into some simple cases for clarity
* if struct <= 24 bytes 
*   if elements contains >1 integral types -> GPRs
*   if elements contains only one type of float
*     if num elements <= 2 -> FPRs
*     else -> GPRs
         

* currently we have 
* r9 = cif->rtype
* r7 = ecif->rvalue
RSREG    DS 0H
         LG 11,16(,9)         rtype->elements
         LA 15,0              have we seen a float yet?
         LA 0,0               have we seen a double yet?
RSLOOP   DS 0H
         LG 12,0(,11)         load the current element, we update
*                             this register in NEXT so it's technically
*                             actually rtype->elements + i
         CGIJE 12,0,RSFPR     if we have NULL, we are done
*                             this means we have all float types
         LA 13,10(,12)        address of rtype->elements[i]->type
         LLH 10,0(,13)        load the type (halfword)
         LGHR 10,10           ensure upper half is clear
         CFI 10,11            if type == FFI_TYPE_FLOAT
         BE NEXTF             check next element
         CFI 10,1             if type == FFI_TYPE_DOUBLE
         BE NEXTD             check next element
*        CFI 10,1             TODO if type == FFI_TYPE_LONGDOUBLE
*        BE NEXT              check next element

         B RSGPR              we have an integral type, use GPRs

NEXTF    DS 0H
         LA 11,8(,11)         increment the pointer to the next element
         LA 15,1              we have seen a float
         CGIJE 0,1,RSGPR      we have a mix of float/double use GPRs
         B RSLOOP             loop back to the top

NEXTD    DS 0H
         LA 11,8(,11)         increment the pointer to the next element
         LA 0,1               we have seen a double
         CGIJE 15,1,RSGPR     we have a mix of float/double use GPRs
         B RSLOOP             loop back to the top


* label if we're using FPRs
RSFPR    DS 0H
         LA 5,0
         LA 15,SSTOR
         LG 11,16(,9)
         LG 12,0(,11)
         CGIJE 12,0,RSCPY
         LA 13,10(,12)        address of rtype->elements[i]->type
         LLH 10,0(,13)        load the type (halfword)
         LGHR 10,10           ensure upper half is clear
         CFI 10,11            if type == FFI_TYPE_FLOAT
         BE STOREF1           store the float in the return area
         CFI 10,1             if type == FFI_TYPE_DOUBLE
         BE STORED1

STOREF1  DS 0H
         STE 0,0(5,15)
         AGFI 5,4
         B STORFPR2

STORED1  DS 0H
         STD 0,0(5,15)
         AGFI 5,8
         B STORFPR2

STORFPR2 DS 0H
         LA 11,8(,11)
         LG 12,0(,11)
         CGIJE 12,0,RSCPY
         LA 13,10(,12)        address of rtype->elements[i]->type
         LLH 10,0(,13)        load the type (halfword)
         LGHR 10,10           ensure upper half is clear
         CFI 10,11            if type == FFI_TYPE_FLOAT
         BE STOREF2           store the float in the return area
         CFI 10,1             if type == FFI_TYPE_DOUBLE
         BE STORED2

STOREF2  DS 0H
         STE 2,0(5,15)
         AGFI 5,4
         B STORFPR3

STORED2  DS 0H
         STD 2,0(5,15)
         AGFI 5,8
         B STORFPR3

STORFPR3 DS 0H

         LA 11,8(,11)
         LG 12,0(,11)
         CGIJE 12,0,RSCPY    if we have NULL, time to copy
         BE RSGPR            if we still have elements we use GPRs

* label if we're using GPRs
RSGPR    DS 0H
* so to save us from having to figure out
* how many regs to save, we'll just save them all
* into some local storage, then copy the right amount
         LA 15,SSTOR      
         STG  1,0(,15)
         STG  2,8(,15)
         STG  3,16(,15)
         B RSCPY

* label to copy the struct to the return area
* just move one byte at a time from r15 to r7
* while r14 is non-zero 

RSCPY    DS 0H 
         CGIJNH 14,0,RET
         LB 1,0(,15)
*         STB 1,0(,7)
         STC 1,0(,7)
         LA 15,1(,15)
         LA 7,1(,7)
         AFI 14,-1
         B RSCPY
 
* return struct in pointer passed as dummy first argument
* this should be the same pointer passed to ffi_call
* and should have been set up in  prep_args
* only using an explicit label for clarity
RSP      DS 0H                 
         B RET                  
  
RET      DS 0H 
         CELQEPLG

ATABLE DC A(I)                Labels for parm types
 DC A(D)       
 DC A(LD)
 DC A(UI8)
 DC A(SI8)
 DC A(UI16)
 DC A(SI16)
 DC A(UI32)
 DC A(SI64)
 DC A(PTR) 
 DC A(UI64)
 DC A(FLT)
 DC A(STRCT)
 DC A(VOID)
 DC A(I)
 DC A(D)
I32 DC A(IGPR1)               Labels for passing INT in gpr
 DC A(IGPR2)
 DC A(IGPR3)
 DC A(IARGA)                  Label to store INT in arg area
I8 DC A(I8GPR1)               Labels for passing CHAR in gpr
 DC A(I8GPR2)
 DC A(I8GPR3)
 DC A(I8ARGA)                 Label to store CHAR in arg area
U16 DC A(U16GPR1)             Labels for passing u_SHORT in gpr
 DC A(U16GPR2)
 DC A(U16GPR3)
 DC A(U16ARGA)                Label to store u_SHORT in arg area
S16 DC A(S16GPR1)             Labels for passing s_SHORT in gpr
 DC A(S16GPR2)
 DC A(S16GPR3)
 DC A(S16ARGA)                Label to store s_SHORT in arg area
S64 DC A(S64GPR1)             Labels to store INT64 in gpr
 DC A(S64GPR2)
 DC A(S64GPR3)
 DC A(S64ARGA)                Label to store INT64 in arg area
PTRS DC A(PTRG1)              Labels to store PTR in gpr
 DC A(PTRG2)
 DC A(PTRG3)
 DC A(PTRARG)                 Label to store PTR in arg area
FLD DC A(FLDR0)               Labels to store DOUBLE in fpr
 DC A(FLDR2)
 DC A(FLDR4)
 DC A(FLDR6)
 DC A(ARGAFL)                 Label to store DOUBLE in arg area
LDD DC A(DFPR0)               Labels to store l_DOUBLE in fpr
 DC A(DFPR4)
 DC A(DARGF)                  Label to store l_DOUBLE in arg area
UI64S DC A(U64GP1)           Labels to store u_INT64 in gpr 
  DC A(U64GP2)
  DC A(U64GP3)
  DC A(U64ARGA)               Label to store u_INT64 in arg area
FLTS DC A(FLTR0)              Labels to store FLOAT in fpr
  DC A(FLTR2)
  DC A(FLTR4)
  DC A(FLTR6)
  DC A(ARGAFT)                Label to store FLOAT in arg area
RTABLE DC A(RV)
 DC A(RS)
 DC A(RF)
 DC A(RD)
 DC A(RLD)
 DC A(RI)
 DC A(RLL) 
RETVOID  EQU  X'0'
RETSTRT  EQU  X'1'
RETFLOT  EQU  X'2'
RETDBLE  EQU  X'3'
RETINT3  EQU  X'4'
RETINT6  EQU  X'5'
OFFSET   EQU  7
BASEREG  EQU  8
GPX      EQU  0
WRKREG   EQU  11    
IDXREG   EQU  10    
STKREG   EQU  13
FPX      EQU  14
CEEDSAHP CEEDSA SECTYPE=XPLINK
ARGSL DS  XL800
LSTOR DS  XL800
* storage space for the returns regs maximum 4*8 fpr
* TODO check long doubles, might be 8*8
SSTOR DS  XL32
SSIZE DS  XL8
DSASZ    EQU (*-CEEDSAHP_FIXED)
 END FFISYS
