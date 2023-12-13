
/*------------------------------------------------------------------------
   File        : totp
   Purpose     :
   Syntax      :
   Description :
   Author(s)   : James
   Created     : Sat Sep 17 11:39:02 NZST 2022
   Notes       : https://github.com/Jimbobnz/ABL-TOTP/tree/main
 ----------------------------------------------------------------------*/

USING Progress.Lang.*.

BLOCK-LEVEL ON ERROR UNDO, THROW.

CLASS System.cls.totp FINAL:

    DEFINE PUBLIC PROPERTY secretKey AS CHARACTER NO-UNDO
        GET.
        PRIVATE SET.

    DEFINE PUBLIC PROPERTY step AS INTEGER INITIAL 30 NO-UNDO
        GET.
        PRIVATE SET.

    DEFINE PUBLIC PROPERTY totpSize AS INTEGER INITIAL 6 NO-UNDO
        GET.
        PRIVATE SET.

    DEFINE PUBLIC PROPERTY hashMode AS CHARACTER INITIAL 'HMAC-SHA-1' NO-UNDO
        GET.
        PRIVATE SET.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    CONSTRUCTOR PUBLIC totp (INPUT secretKey AS CHARACTER  ):
        SUPER ().

        THIS-OBJECT:secretKey = secretKey.

    END CONSTRUCTOR.

    CONSTRUCTOR PUBLIC totp (INPUT secretKey AS CHARACTER, INPUT step AS INTEGER  ):
        SUPER ().

        THIS-OBJECT:secretKey = secretKey.
        THIS-OBJECT:step      = step.


    END CONSTRUCTOR.

    CONSTRUCTOR PUBLIC totp (INPUT secretKey AS CHARACTER, INPUT step AS INTEGER, INPUT totpSize AS INTEGER ):
        SUPER ().

        THIS-OBJECT:secretKey = secretKey.
        THIS-OBJECT:step      = step.
        THIS-OBJECT:totpSize  = totpSize.

    END CONSTRUCTOR.

    CONSTRUCTOR PUBLIC totp (INPUT secretKey AS CHARACTER, INPUT step AS INTEGER, INPUT totpSize AS INTEGER, INPUT hashMode AS CHARACTER  ):
        SUPER ().

        THIS-OBJECT:secretKey = secretKey.
        THIS-OBJECT:step      = step.
        THIS-OBJECT:totpSize  = totpSize.
        THIS-OBJECT:hashMode  = hashMode.

    END CONSTRUCTOR.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER arithmeticLeftShift( INPUT x AS INTEGER, INPUT z AS INTEGER):


        DEFINE VARIABLE ishift AS INTEGER NO-UNDO.
        DEFINE VARIABLE y      AS INTEGER NO-UNDO.

        DO ishift = 1 TO z:

            PUT-BITS(y, 2, 31) = GET-BITS(x, 1, 31).
            PUT-BITS(y, 1, 1)  = 0.  // The empty position in the least significant bit is filled with a zero.

            x = y.

        END.

        RETURN x.
    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INT64 arithmeticLeftShift64(INPUT x AS INT64, INPUT z AS INTEGER):


        DEFINE VARIABLE ishift AS INTEGER NO-UNDO.
        DEFINE VARIABLE y      AS INT64   NO-UNDO.

        DO ishift = 1 TO z:

            PUT-BITS(y, 2, 31) = GET-BITS(x, 1, 31).
            PUT-BITS(y, 1, 1)  = 0.  // The empty position in the least significant bit is filled with a zero.

            x = y.

        END.

        RETURN x.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER arithmeticRightShift( INPUT x AS INTEGER, INPUT z AS INTEGER):

        DEFINE VARIABLE ishift AS INTEGER NO-UNDO.
        DEFINE VARIABLE y      AS INTEGER NO-UNDO.

        DO ishift = 1 TO z:

            PUT-BITS(y, 32, 1) = GET-BITS(x, 32, 1).   //The empty position in the most significant bit is filled with a copy of the original MSB
            PUT-BITS(y, 1, 31) = GET-BITS(x, 2, 31).

            x = y.

        END.

        RETURN x.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE MEMPTR base32Decode( INPUT base32EncodedValue AS CHARACTER):

        DEFINE VARIABLE returnArray       AS MEMPTR    NO-UNDO.

        DEFINE VARIABLE chCharByte        AS CHARACTER NO-UNDO.

        DEFINE VARIABLE iValue            AS INTEGER   NO-UNDO.
        DEFINE VARIABLE characterPosition AS INTEGER   NO-UNDO.
        DEFINE VARIABLE iLength           AS INTEGER   NO-UNDO.
        DEFINE VARIABLE iByteCount        AS INTEGER   NO-UNDO.
        DEFINE VARIABLE iBitsRemaining    AS INTEGER   NO-UNDO.
        DEFINE VARIABLE iMask             AS INTEGER   NO-UNDO.
        DEFINE VARIABLE iCurrentByte      AS INTEGER   NO-UNDO.
        DEFINE VARIABLE bytePosition      AS INTEGER   NO-UNDO.

        set-byte-order(returnArray ) = BIG-ENDIAN.

        IF base32EncodedValue EQ "" THEN
            RETURN ?.

        ASSIGN
            base32EncodedValue = REPLACE(base32EncodedValue,' ','')
            base32EncodedValue = REPLACE(base32EncodedValue,'=','')
            base32EncodedValue = TRIM(base32EncodedValue)
            .

        ASSIGN
            iLength    = LENGTH(base32EncodedValue,"RAW")
            iByteCount = TRUNCATE(iLength * 5 / 8,0)
            .

        SET-SIZE(returnArray ) = 0.
        SET-SIZE(returnArray ) = iByteCount.

        ASSIGN
            iBitsRemaining = 8
            iMask          = 0
            iCurrentByte   = 0
            bytePosition   = 0
            .

        DO characterPosition = 1 TO iLength:

            chCharByte = SUBSTRING(base32EncodedValue, characterPosition, 1, "RAW").

            iValue = THIS-OBJECT:charToValue(INPUT chCharByte).

            IF iValue EQ ? THEN
                NEXT.

            IF iBitsRemaining GT 5 THEN
            DO:
                ASSIGN
                    iMask          = THIS-OBJECT:arithmeticLeftShift(iValue , (iBitsRemaining - 5) )
                    iCurrentByte   = THIS-OBJECT:bitOR(iCurrentByte, iMask)
                    iBitsRemaining = iBitsRemaining - 5
                    .

            END.
            ELSE
            DO:

                ASSIGN
                    iMask        = THIS-OBJECT:arithmeticRightShift(iValue , (5 - iBitsRemaining) )
                    iCurrentByte = THIS-OBJECT:bitOR(iCurrentByte, iMask)
                    bytePosition = bytePosition + 1
                    .

                put-byte(returnArray, bytePosition) = iCurrentByte.

                ASSIGN
                    iCurrentByte = THIS-OBJECT:arithmeticLeftShift(iValue , (3 + iBitsRemaining) ).
                iBitsRemaining = iBitsRemaining + 3
                    .
            END.
        END.

        IF bytePosition NE iByteCount THEN
        DO:
            bytePosition  = bytePosition + 1.
            put-byte(returnArray, bytePosition) = iCurrentByte.

        END.

        RETURN returnArray.

        FINALLY:

            SET-SIZE(returnArray) = 0.

        END FINALLY.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER bitAnd( INPUT X AS INTEGER, INPUT Y AS INTEGER):

        DEFINE VARIABLE b AS INTEGER NO-UNDO.
        DEFINE VARIABLE n AS INTEGER NO-UNDO.
        DEFINE VARIABLE Z AS INTEGER NO-UNDO.

        DO n = 1 TO 32:

            IF GET-BITS(X, n, 1) = 1 AND get-bits(Y, n, 1) = 1 THEN
                b = 1.

            PUT-BITS(Z, n, 1) = b.
            b = 0.

        END.

        RETURN Z.
    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INT64 bitAnd64( INPUT X AS INT64, INPUT Y AS INT64):

        DEFINE VARIABLE b AS INTEGER NO-UNDO.
        DEFINE VARIABLE n AS INTEGER NO-UNDO.
        DEFINE VARIABLE Z AS INT64   NO-UNDO.

        DO n = 1 TO 64:

            IF GET-BITS(X, n, 1) = 1 AND get-bits(Y, n, 1) = 1 THEN
                b = 1.

            PUT-BITS(Z, n, 1) = b.
            b = 0.

        END.

        RETURN Z.
    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER bitOR( INPUT X AS INTEGER, INPUT Y AS INTEGER):

        DEFINE VARIABLE n AS INTEGER NO-UNDO.
        DEFINE VARIABLE Z AS INTEGER NO-UNDO.

        DO n = 1 TO 32:

            IF GET-BITS(X, n, 1) = 1 OR get-bits(Y, n, 1) = 1 THEN
                PUT-BITS(Z, n, 1) = 1.

        END.

        RETURN Z.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INT64 bitOR64(INPUT X AS INT64, INPUT Y AS INT64):

        DEFINE VARIABLE n AS INTEGER NO-UNDO.
        DEFINE VARIABLE Z AS INT64   NO-UNDO.

        DO n = 1 TO 64:

            IF GET-BITS(X, n, 1) EQ 1 OR get-bits(Y, n, 1) EQ 1 THEN
                PUT-BITS(Z, n, 1) = 1.

        END.

        RETURN Z.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INT64 calculateTimeStepFromTimestamp( INPUT Timestamp AS INT64 ):

/*        define variable TimeStep as integer no-undo.         */
/*                                                             */
/*        TimeStep = truncate(Timestamp / this-object:step, 0).*/

        RETURN INT64(TRUNCATE(Timestamp / THIS-OBJECT:step, 0)) .

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER charToValue(  INPUT charByte AS CHARACTER):

        DEFINE VARIABLE charByteValue AS INTEGER NO-UNDO.

        charByteValue = ASC(charByte).

    //65-90 == uppercase letters
        IF charByteValue LT 91 AND charByteValue GT 64 THEN
            RETURN charByteValue - 65.

    //50-55 == numbers 2-7
        IF charByteValue LT 56 AND charByteValue GT 49 THEN
            RETURN charByteValue - 24.

    //97-122 == lowercase letters
        IF(charByteValue LT 123 AND charByteValue GT 96) THEN
            RETURN charByteValue - 97.

        RETURN ?.

    END METHOD.


  METHOD PUBLIC LOGICAL CheckTotp
    (INPUT  pcTotp    AS CHARACTER      ):

    RETURN THIS-OBJECT:CheckTotp(pcTotp, 1). /* Default check for +/- 1 code; this means that both slow typing and (small) differences in time are allowed */

  END METHOD.


  METHOD PUBLIC LOGICAL CheckTotp
    (INPUT  pcTotp    AS CHARACTER
    ,INPUT  piExtra   AS INTEGER        ):

    /* Check if the manually entered TOTP is valid. piExtra is the number of codes (up and down) that are allowed */

    IF LENGTH(pcTotp) NE THIS-OBJECT:totpSize
    THEN RETURN FALSE.

    IF LOOKUP(pcTotp, THIS-OBJECT:GenerateTotpList(piExtra)) GT 0
    THEN RETURN TRUE.
    ELSE RETURN FALSE.

  END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PUBLIC CHARACTER ComputeTotp(  ):

      RETURN THIS-OBJECT:GenerateTotpList(0).

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INTEGER dynamicTruncate( INPUT hashResult AS MEMPTR ):

        DEFINE VARIABLE byteOffset    AS INTEGER NO-UNDO.
        DEFINE VARIABLE bytePosition  AS INTEGER NO-UNDO.

        DEFINE VARIABLE truncatedHash AS INTEGER NO-UNDO.
        DEFINE VARIABLE inBinary      AS INT64   NO-UNDO.

        ASSIGN
            byteOffset = GET-BYTE(hashResult, 20)     //Get the last byte
            byteOffset = THIS-OBJECT:bitAnd(byteOffset, 0x0F)     //get the last 4 bits
            .

        inBinary = 0.

        DO bytePosition = 1 TO 4:

            ASSIGN
                inBinary = THIS-OBJECT:arithmeticLeftShift64(inBinary , 8)
                inBinary = THIS-OBJECT:bitOR64(inBinary, GET-BYTE(hashResult, byteOffset + bytePosition) )
                .

        END.

        ASSIGN
            inBinary      = THIS-OBJECT:bitAnd64(inBinary, 0x7FFFFFFF)
            truncatedHash = inBinary MOD 0xF4240
            .

        RETURN truncatedHash.

    END METHOD.


  METHOD PRIVATE CHARACTER GenerateTotp( ):
    RETURN GenerateTotpList(0).
  END METHOD.


  METHOD PRIVATE CHARACTER GenerateTotpList
    (INPUT piExtra    AS INTEGER   ):

    DEFINE VARIABLE timestamp       AS INT64     NO-UNDO.
    DEFINE VARIABLE timeStep        AS INTEGER   NO-UNDO.
    DEFINE VARIABLE timeStepLoop    AS INTEGER   NO-UNDO.
    DEFINE VARIABLE TOTPCode        AS INTEGER   NO-UNDO.
    DEFINE VARIABLE hashResult      AS MEMPTR    NO-UNDO.
    DEFINE VARIABLE counterMemptr   AS MEMPTR    NO-UNDO.
    DEFINE VARIABLE secretKeyMemptr AS MEMPTR    NO-UNDO.
    DEFINE VARIABLE computeTotp     AS CHARACTER NO-UNDO.
    DEFINE VARIABLE iLoop           AS INTEGER   NO-UNDO.
    DEFINE VARIABLE cTotpList       AS CHARACTER NO-UNDO.
    DEFINE VARIABLE iLoopMultiply   AS INTEGER   NO-UNDO.

    THIS-OBJECT:verifyParameters().

    SET-BYTE-ORDER(hashResult)      = BIG-ENDIAN.
    SET-BYTE-ORDER(counterMemptr)    = BIG-ENDIAN.
    SET-BYTE-ORDER(secretKeyMemptr)  = BIG-ENDIAN.

    SET-SIZE(hashResult)      = 0.
    SET-SIZE(secretKeyMemptr)  = 0.
    SET-SIZE(counterMemptr)    = 0.
    SET-SIZE(counterMemptr)    = 8. // 8 bytes = 64 bits

    ASSIGN
      secretKeyMemptr = THIS-OBJECT:base32decode(INPUT THIS-OBJECT:secretKey)
      timestamp       = THIS-OBJECT:unixTime()
      timeStep        = THIS-OBJECT:calculateTimeStepFromTimestamp(INPUT timestamp)
      .

    DO iLoop = 1 TO 1 + (2 * piExtra):
      IF iLoop GT 1
      THEN DO:
        IF iLoop MOD 2 EQ 0
        THEN ASSIGN
              iLoopMultiply = (iLoop - 0) / 2
              timeStepLoop = timeStep - (1 * iLoopMultiply)
              .
        ELSE ASSIGN
               iLoopMultiply = (iLoop - 1) / 2
               timeStepLoop = timeStep + (1 * iLoopMultiply)
               .
      END.
      ELSE timeStepLoop = timeStep.

      PUT-INT64(counterMemptr,1) = timeStepLoop.

      ASSIGN
        hashResult  = MESSAGE-DIGEST(THIS-OBJECT:hashMode, counterMemptr, secretKeyMemptr)
        TOTPCode    = THIS-OBJECT:dynamicTruncate(INPUT  hashResult)
        computeTotp = STRING(TOTPCode, "99999999")
        computeTotp = SUBSTRING( computeTotp, (LENGTH(computeTotp) - THIS-OBJECT:totpSize) + 1, THIS-OBJECT:totpSize )
        cTotpList   = IF cTotpList EQ "" THEN computeTotp ELSE cTotpList + "," + computeTotp
        .
    END.

    RETURN cTotpList.

    FINALLY:

      //SET-SIZE(hashResult) = 0.
      //SET-SIZE(secretkey)  = 0.
      //SET-SIZE(counter)    = 0.

    END FINALLY.

  END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PUBLIC INTEGER remainingSeconds(  ):

        DEFINE VARIABLE remainingSeconds AS INTEGER NO-UNDO.

        ASSIGN
            remainingSeconds = TIME MOD 60
            remainingSeconds = (30 - (remainingSeconds MOD 30)).

        RETURN remainingSeconds.

    END METHOD.


    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE INT64 unixTime(  ):

        DEFINE VARIABLE localTime     AS DATETIME-TZ NO-UNDO.
        DEFINE VARIABLE utcTime       AS DATETIME-TZ NO-UNDO.
        DEFINE VARIABLE epocTime      AS DATETIME-TZ NO-UNDO.
        DEFINE VARIABLE unixTime      AS INTEGER     NO-UNDO.
        DEFINE VARIABLE timeremaining AS INTEGER     NO-UNDO.

        ASSIGN
            epocTime  = DATETIME-TZ(1,1,1970,0,0,0,0,0) // Epoch
            localTime = NOW                             // local time of the current machine
            utcTime   = DATETIME-TZ(localTime, 0)       // Convert the localtime to UTC +00:00
            unixTime  = INTERVAL( utcTime, epocTime, 'seconds' )
            .

        RETURN unixTime.

    END METHOD.

    /*------------------------------------------------------------------------------
     Purpose:
     Notes:
    ------------------------------------------------------------------------------*/

    METHOD PRIVATE VOID verifyParameters(  ):

        IF  NOT (THIS-OBJECT:step > 0) THEN
            RETURN ERROR NEW Progress.Lang.AppError("Step must be a positive value" ).

        IF NOT (THIS-OBJECT:totpSize > 0) THEN
            RETURN ERROR NEW Progress.Lang.AppError("totpSize must be a positive value" ).

        IF NOT (THIS-OBJECT:totpSize <= 10) THEN
            RETURN ERROR NEW Progress.Lang.AppError("totpSize must be less or equal to 10" ).

        RETURN.

    END METHOD.

    DESTRUCTOR PUBLIC totp ( ):

    END DESTRUCTOR.

END CLASS.
