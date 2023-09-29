{-# LANGUAGE DataKinds #-}

-- Promoted to type-level, i.e. Kinds and Types
data UserType = User | Admin
    deriving (Show)

-- UserType here is the kind promoted from the datatype definition above
data Token (a :: UserType) = Token
    deriving (Show)

data Result = Secret | Normal
    deriving (Show)

secretOp :: Token 'Admin -> Result
secretOp _ = Secret

normalOp :: Token a -> Result
normalOp _ = Normal

tokenA = Token :: Token 'Admin

tokenU = Token :: Token 'User

-- succeed
test1 = secretOp tokenA

-- fail type-checking
-- test2 = secretOp tokenU

-- succeed
test3 = normalOp tokenA

-- succeed
test4 = normalOp tokenU
