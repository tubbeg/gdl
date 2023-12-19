(ns gdl.app
  (:require [gdl.screen :as screen]
            [gdl.context :refer [current-screen change-screen update-viewports fix-viewport-update]])
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.graphics.Color
           com.badlogic.gdx.utils.ScreenUtils))

(extend-type com.badlogic.gdx.utils.Disposable
  gdl.disposable/Disposable
  (dispose [this]
    (.dispose this)))

(defn- dispose-all [context]
  (doseq [[k value] context
          :when (some #(extends? gdl.disposable/Disposable %)
                      (supers (class value)))]
    (println "Disposing " k)
    (gdl.disposable/dispose value)))

(extend-type gdl.context.Context
  gdl.context/ApplicationScreens
  (current-screen [{:keys [context/current-screen] :as context}]
    (get context current-screen))

  (change-screen [context new-screen-key]
    (when-let [screen (current-screen context)]
      (screen/hide screen context)
      (screen/hide screen context))
    (let [screen (new-screen-key context)
          _ (assert screen (str "Cannot find screen with key: " new-screen-key))
          new-context (assoc context :context/current-screen new-screen-key)]
      (screen/show screen new-context)
      new-context)))

(defn- ->application [{:keys [current-context create-context first-screen]}]
  (assert current-context ":current-context key not supplied")
  (assert create-context ":create-context key not supplied")
  (assert first-screen ":first-screen key not supplied")
  (proxy [ApplicationAdapter] []
    (create []
      (reset! current-context (change-screen (create-context) first-screen)))
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
  and :context-fn / :first-screen.
  TODO describe the whole app-lifecycle
  e.g. create , dispose, resize, render ... like in libgdx
  => point to libgdx docs.
  "
  [config]
  ; TODO assert create-context / current-context
  (Lwjgl3Application. (->application config)
                      (lwjgl3-configuration (:app config))))
