(ns gdx.lwjgl
  (:import [com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration]))

(defn create-app
  [& {:keys [game
             title
             width
             height
             full-screen] :as args}]
  (let [config (Lwjgl3ApplicationConfiguration.)]
    (.setTitle config title)
    (.setForegroundFPS config 30) ; TODO do not config this here ...
    (if full-screen
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    ;(println "Starting Lwjgl3Application"); TODO logging
    (Lwjgl3Application. game config)))
