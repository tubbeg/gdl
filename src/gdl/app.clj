(ns gdl.app
  (:require [gdl.screen :as screen]
            [gdl.context :refer [dispose-all current-screen
                                 update-viewports ; on-resize (implemented by views)
                                 fix-viewport-update ; pre-render-hook (implemented by views)
                                 ]])
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.graphics.Color
           com.badlogic.gdx.utils.ScreenUtils))

(defn- ->application [{:keys [current-context create-context]}]
  (proxy [ApplicationAdapter] []
    (create []
      (reset! current-context (create-context)))
    (dispose []
      (dispose-all @current-context))
    (render []
      (ScreenUtils/clear Color/BLACK)
      (let [context @current-context
            screen (current-screen context)]
        (fix-viewport-update context)
        (screen/render screen context)
        (screen/tick screen context (* (.getDeltaTime Gdx/graphics) 1000))))
    (resize [w h]
      (update-viewports @current-context w h))))

(defn- lwjgl3-configuration [{:keys [title width height full-screen? fps]}]
  ; https://github.com/trptr/java-wrapper/blob/39a0947f4e90857512c1999537d0de83d130c001/src/trptr/java_wrapper/locale.clj#L87
  ; cond->
  (let [config (doto (Lwjgl3ApplicationConfiguration.)
                 (.setTitle title)
                 (.setForegroundFPS (or fps 60)))]
    (if full-screen?
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    config))

(defn start
  "Starts a lwjgl3 application with configs
  {:app {:keys [title width height full-screen? fps]}}
  ; TODO fix fps limiting off by default
  and :context-fn / :first-screen."
  [config]
  (Lwjgl3Application. (->application config)
                      (lwjgl3-configuration (:app config))))
