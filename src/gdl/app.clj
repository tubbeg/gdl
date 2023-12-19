(ns gdl.app
  (:require [gdl.screen :as screen]
            gdl.context
            gdl.disposable)
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.graphics.Color
           com.badlogic.gdx.utils.ScreenUtils))

(defn- current-screen [{:keys [context/current-screen] :as context}]
  (get context current-screen))

; TODO hide and show could also be functions returning and altering context?!
(defn change-screen
  "Fetches the new screen from context via get.
  Calls screen/hide on the previous screen.
  Calls screen/show on the new screen and sets it as :context/current-screen
  Throws assertionerror when the context does not have a screen with new-screen-key."
  [context new-screen-key]
  (when-let [screen (current-screen context)]
    (screen/hide screen context))
  (let [screen (new-screen-key context)
        _ (assert screen (str "Cannot find screen with key: " new-screen-key))
        new-context (assoc context :context/current-screen new-screen-key)]
    (screen/show screen new-context)
    new-context))

(extend-type com.badlogic.gdx.utils.Disposable
  gdl.disposable/Disposable
  (dispose [this]
    (.dispose this)))

(defn- dispose-context [context]
  (doseq [[k value] context
          :when (some #(extends? gdl.disposable/Disposable %)
                      (supers (class value)))]
    (println "Disposing " k)
    (gdl.disposable/dispose value)))

; TODO could adjust ApplicationAdapter to pass an object (context) and keep it
; but how do I access it? and what state will it have at a point in time ? it should be an atom ...
(defn- application-adapter [{:keys [current-context context-fn first-screen]}]
  (proxy [ApplicationAdapter] []
    (create []
      (reset! current-context
              (change-screen (context-fn) first-screen)))
    (dispose []
      (dispose-context @current-context))
    (render []
      (ScreenUtils/clear Color/BLACK)
      (let [context @current-context
            screen (current-screen context)]
        (gdl.context/fix-viewport-update context)
        (screen/render screen context)
        ; TODO the big thing - tick could return a new context ...
        (screen/tick screen context (* (.getDeltaTime Gdx/graphics) 1000))))
    (resize [w h]
      (gdl.context/update-viewports @current-context w h))))

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
  (Lwjgl3Application. (application-adapter config)
                      (lwjgl3-configuration (:app config))))
