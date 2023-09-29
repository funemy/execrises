{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Data.Proxy

-- The code below doesn't type check
-- sr :: String -> String
-- sr = show . read

sr' :: forall proxy a. (Show a, Read a) => proxy a -> String -> String
sr' _ = (show @a) . read

test1 :: String
test1 = sr' (Proxy @Int) "123"

-- The code above can be further simplified with AllowAmbiguousTypes
sr'' :: forall a. (Show a, Read a) => String -> String
sr'' = (show @a) . read

test2 :: String
test2 = sr'' @Int "123"