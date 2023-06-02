
module Agda.Syntax.Treeless
  ( module Agda.Syntax.Treeless
  ) where

import Control.DeepSeq

import Agda.Utils.Pretty
import Agda.Syntax.Position

data Compiled

instance Pretty Compiled
instance Show Compiled
instance KillRange Compiled
instance NFData Compiled

