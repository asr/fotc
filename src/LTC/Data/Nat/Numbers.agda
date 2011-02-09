------------------------------------------------------------------------------
-- Naturales numbers terms
------------------------------------------------------------------------------

module LTC.Data.Nat.Numbers where

open import LTC.Base

------------------------------------------------------------------------------

one    = succ zero
two    = succ one
three  = succ two
four   = succ three
five   = succ four
six    = succ five
seven  = succ six
eight  = succ seven
nine   = succ eight
ten    = succ nine

{-# ATP definition one #-}
{-# ATP definition two #-}
{-# ATP definition three #-}
{-# ATP definition four #-}
{-# ATP definition five #-}
{-# ATP definition six #-}
{-# ATP definition seven #-}
{-# ATP definition eight #-}
{-# ATP definition nine #-}
{-# ATP definition ten #-}

eleven    = succ ten
twelve    = succ eleven
thirteen  = succ twelve
fourteen  = succ thirteen
fifteen   = succ fourteen
sixteen   = succ fifteen
seventeen = succ sixteen
eighteen  = succ seventeen
nineteen  = succ eighteen
twenty    = succ nineteen

{-# ATP definition eleven #-}
{-# ATP definition twelve #-}
{-# ATP definition thirteen #-}
{-# ATP definition fourteen #-}
{-# ATP definition fifteen #-}
{-# ATP definition sixteen #-}
{-# ATP definition seventeen #-}
{-# ATP definition eighteen #-}
{-# ATP definition nineteen #-}
{-# ATP definition twenty #-}

twenty-one   = succ twenty
twenty-two   = succ twenty-one
twenty-three = succ twenty-two
twenty-four  = succ twenty-three
twenty-five  = succ twenty-four
twenty-six   = succ twenty-five
twenty-seven = succ twenty-six
twenty-eight = succ twenty-seven
twenty-nine  = succ twenty-eight
thirty       = succ twenty-nine

{-# ATP definition twenty-one #-}
{-# ATP definition twenty-two #-}
{-# ATP definition twenty-three #-}
{-# ATP definition twenty-four #-}
{-# ATP definition twenty-five #-}
{-# ATP definition twenty-six #-}
{-# ATP definition twenty-seven #-}
{-# ATP definition twenty-eight #-}
{-# ATP definition twenty-nine #-}
{-# ATP definition thirty #-}

thirty-one   = succ thirty
thirty-two   = succ thirty-one
thirty-three = succ thirty-two
thirty-four  = succ thirty-three
thirty-five  = succ thirty-four
thirty-six   = succ thirty-five
thirty-seven = succ thirty-six
thirty-eight = succ thirty-seven
thirty-nine  = succ thirty-eight
forty        = succ thirty-nine

{-# ATP definition thirty-one #-}
{-# ATP definition thirty-two #-}
{-# ATP definition thirty-three #-}
{-# ATP definition thirty-four #-}
{-# ATP definition thirty-five #-}
{-# ATP definition thirty-six #-}
{-# ATP definition thirty-seven #-}
{-# ATP definition thirty-eight #-}
{-# ATP definition thirty-nine #-}
{-# ATP definition forty #-}

forty-one   = succ forty
forty-two   = succ forty-one
forty-three = succ forty-two
forty-four  = succ forty-three
forty-five  = succ forty-four
forty-six   = succ forty-five
forty-seven = succ forty-six
forty-eight = succ forty-seven
forty-nine  = succ forty-eight
fifty       = succ forty-nine

{-# ATP definition forty-one #-}
{-# ATP definition forty-two #-}
{-# ATP definition forty-three #-}
{-# ATP definition forty-four #-}
{-# ATP definition forty-five #-}
{-# ATP definition forty-six #-}
{-# ATP definition forty-seven #-}
{-# ATP definition forty-eight #-}
{-# ATP definition forty-nine #-}
{-# ATP definition fifty #-}

fifty-one   = succ fifty
fifty-two   = succ fifty-one
fifty-three = succ fifty-two
fifty-four  = succ fifty-three
fifty-five  = succ fifty-four
fifty-six   = succ fifty-five
fifty-seven = succ fifty-six
fifty-eight = succ fifty-seven
fifty-nine  = succ fifty-eight
sixty       = succ fifty-nine

{-# ATP definition fifty-one #-}
{-# ATP definition fifty-two #-}
{-# ATP definition fifty-three #-}
{-# ATP definition fifty-four #-}
{-# ATP definition fifty-five #-}
{-# ATP definition fifty-six #-}
{-# ATP definition fifty-seven #-}
{-# ATP definition fifty-eight #-}
{-# ATP definition fifty-nine #-}
{-# ATP definition sixty #-}

sixty-one   = succ sixty
sixty-two   = succ sixty-one
sixty-three = succ sixty-two
sixty-four  = succ sixty-three
sixty-five  = succ sixty-four
sixty-six   = succ sixty-five
sixty-seven = succ sixty-six
sixty-eight = succ sixty-seven
sixty-nine  = succ sixty-eight
seventy     = succ sixty-nine

{-# ATP definition sixty-one #-}
{-# ATP definition sixty-two #-}
{-# ATP definition sixty-three #-}
{-# ATP definition sixty-four #-}
{-# ATP definition sixty-five #-}
{-# ATP definition sixty-six #-}
{-# ATP definition sixty-seven #-}
{-# ATP definition sixty-eight #-}
{-# ATP definition sixty-nine #-}
{-# ATP definition seventy #-}

seventy-one   = succ seventy
seventy-two   = succ seventy-one
seventy-three = succ seventy-two
seventy-four  = succ seventy-three
seventy-five  = succ seventy-four
seventy-six   = succ seventy-five
seventy-seven = succ seventy-six
seventy-eight = succ seventy-seven
seventy-nine  = succ seventy-eight
eighty        = succ seventy-nine

{-# ATP definition seventy-one #-}
{-# ATP definition seventy-two #-}
{-# ATP definition seventy-three #-}
{-# ATP definition seventy-four #-}
{-# ATP definition seventy-five #-}
{-# ATP definition seventy-six #-}
{-# ATP definition seventy-seven #-}
{-# ATP definition seventy-eight #-}
{-# ATP definition seventy-nine #-}
{-# ATP definition eighty #-}

eighty-one   = succ eighty
eighty-two   = succ eighty-one
eighty-three = succ eighty-two
eighty-four  = succ eighty-three
eighty-five  = succ eighty-four
eighty-six   = succ eighty-five
eighty-seven = succ eighty-six
eighty-eight = succ eighty-seven
eighty-nine  = succ eighty-eight
ninety       = succ eighty-nine

{-# ATP definition eighty-one #-}
{-# ATP definition eighty-two #-}
{-# ATP definition eighty-three #-}
{-# ATP definition eighty-four #-}
{-# ATP definition eighty-five #-}
{-# ATP definition eighty-six #-}
{-# ATP definition eighty-seven #-}
{-# ATP definition eighty-eight #-}
{-# ATP definition eighty-nine #-}
{-# ATP definition ninety #-}

ninety-one   = succ ninety
ninety-two   = succ ninety-one
ninety-three = succ ninety-two
ninety-four  = succ ninety-three
ninety-five  = succ ninety-four
ninety-six   = succ ninety-five
ninety-seven = succ ninety-six
ninety-eight = succ ninety-seven
ninety-nine  = succ ninety-eight
one-hundred  = succ ninety-nine

{-# ATP definition ninety-one #-}
{-# ATP definition ninety-two #-}
{-# ATP definition ninety-three #-}
{-# ATP definition ninety-four #-}
{-# ATP definition ninety-five #-}
{-# ATP definition ninety-six #-}
{-# ATP definition ninety-seven #-}
{-# ATP definition ninety-eight #-}
{-# ATP definition ninety-nine #-}
{-# ATP definition one-hundred #-}

hundred-one   = succ one-hundred
hundred-two   = succ hundred-one
hundred-three = succ hundred-two
hundred-four  = succ hundred-three
hundred-five  = succ hundred-four
hundred-six   = succ hundred-five
hundred-seven = succ hundred-six
hundred-eight = succ hundred-seven
hundred-nine  = succ hundred-eight
hundred-ten   = succ hundred-nine

{-# ATP definition hundred-one #-}
{-# ATP definition hundred-two #-}
{-# ATP definition hundred-three #-}
{-# ATP definition hundred-four #-}
{-# ATP definition hundred-five #-}
{-# ATP definition hundred-six #-}
{-# ATP definition hundred-seven #-}
{-# ATP definition hundred-eight #-}
{-# ATP definition hundred-nine #-}
{-# ATP definition hundred-ten #-}

hundred-eleven = succ hundred-ten
{-# ATP definition hundred-eleven #-}
