{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_probabilitypresentation (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [1,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/doisinkidney/Library/Haskell/bin"
libdir     = "/Users/doisinkidney/Library/Containers/com.haskellformac.Haskell.basic/Data/Library/Application Support/lib/ghc/probabilitypresentation-1.0-F57JnNmaIxKLGRM1SH4b9B"
dynlibdir  = "/Users/doisinkidney/Library/Containers/com.haskellformac.Haskell.basic/Data/Library/Application Support/lib/ghc/probabilitypresentation-1.0-F57JnNmaIxKLGRM1SH4b9B"
datadir    = "/Users/doisinkidney/Library/Containers/com.haskellformac.Haskell.basic/Data/Library/Application Support/share/probabilitypresentation-1.0"
libexecdir = "/Users/doisinkidney/Library/Containers/com.haskellformac.Haskell.basic/Data/Library/Application Support/libexec"
sysconfdir = "/Users/doisinkidney/Library/Containers/com.haskellformac.Haskell.basic/Data/Library/Application Support/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "probabilitypresentation_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "probabilitypresentation_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "probabilitypresentation_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "probabilitypresentation_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "probabilitypresentation_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "probabilitypresentation_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
