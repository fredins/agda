
module Agda.Compiler.Backend
  ( Backend
  , activeBackendMayEraseType
  , lookupBackend
  )
  where

import Control.DeepSeq

import Agda.Syntax.Abstract.Name (QName)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base (TCM, BackendName)

data Backend

instance NFData Backend

activeBackendMayEraseType :: QName -> TCM Bool
lookupBackend :: BackendName -> TCM (Maybe Backend)
