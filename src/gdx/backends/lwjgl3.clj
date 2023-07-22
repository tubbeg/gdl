(ns gdx.backends.lwjgl3
  (:import [com.badlogic.gdx.backends.lwjgl3
            Lwjgl3Application
            Lwjgl3ApplicationConfiguration]
           [com.badlogic.gdx.utils
            SharedLibraryLoader]))

; TODO 'full-screen?'
(defn- configuration [{:keys [title width height full-screen fps]}]
  #_(when SharedLibraryLoader/isMac
      (mac-dock-icon/set-mac-os-dock-icon))

  ; https://github.com/trptr/java-wrapper/blob/39a0947f4e90857512c1999537d0de83d130c001/src/trptr/java_wrapper/locale.clj#L87
  ; cond->
  (let [config (doto (Lwjgl3ApplicationConfiguration.)
                 (.setTitle title)
                 (.setForegroundFPS (or fps 60)))]
    (if full-screen
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    config))

; TODO docstring
(defn create-app [game config]
  (Lwjgl3Application. game (configuration config)))
