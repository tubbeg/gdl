(ns gdl.backends.libgdx.app
  (:require [gdl.app :refer [current-context]]
            [gdl.context :as ctx]
            [gdl.disposable :refer [dispose]]
            [gdl.graphics.color :as color]
            [gdl.screen :as screen]
            (gdl.backends.libgdx.context [assets :as assets]
                                         [graphics :as graphics]
                                         input
                                         image-drawer-creator
                                         stage
                                         tiled
                                         ttf-generator
                                         [vis-ui :as vis-ui]))
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.utils.ScreenUtils))

(extend-type gdl.context.Context
  gdl.context/Application
  (exit-app [_]
    (.exit Gdx/app)))

#_(defn- assert-module-loaded [k]
  (let [ns-sym (-> k name symbol)]
    (assert (find-ns ns-sym)
            (str "Cannot find module namespace " ns-sym))))

; TODO :context/assets false does still load
; also [:context/assets] w/o args possible
(defn- ->context [context]
  (assert (apply distinct? (map first context)))
  (when true ;log-context-component-create?
    (println "ctx/create "))
  (reduce (fn [ctx {k 0 :as component}]
            (when true ;log-context-component-create?
              (println k))
            #_(assert-module-loaded k) ; TODO also asserts component exists ! do this maybe first w. schema or sth.
            ; TODO safe-merge? ( distinct keys, not necessary....)
            (merge ctx [k (ctx/create component ctx)]))
          (ctx/->Context)
          context))

(extend-type com.badlogic.gdx.utils.Disposable
  gdl.disposable/Disposable
  (dispose [this]
    (.dispose this)))

(defn- dispose-all [context]
  (doseq [[k value] context
          :when (or (extends? gdl.disposable/Disposable (class value))
                    (some #(extends? gdl.disposable/Disposable %)
                          (supers (class value))))]
    ;(println "Disposing " k)
    (dispose value)))

(extend-type gdl.context.Context
  gdl.context/ApplicationScreens
  (current-screen [{{:keys [current-screen] :as screens} :context/screens}]
    (get screens current-screen))

  (change-screen [{{:keys [current-screen] :as screens} :context/screens :as context}
                  new-screen-key]
    (when-let [screen (and current-screen
                           (current-screen screens))]
      (screen/hide screen context))
    (let [screen (new-screen-key screens)
          _ (assert screen (str "Cannot find screen with key: " new-screen-key))
          new-context (assoc-in context [:context/screens :current-screen] new-screen-key)]
      (screen/show screen new-context)
      new-context)))

(defn- ->application [{:keys [context]}]
  (proxy [ApplicationAdapter] []
    (create []
      (let [context (->context context)]
        (assert (:first-screen (:context/screens context)))
        (->> context
             :context/screens
             :first-screen
             (ctx/change-screen context)
             (reset! current-context))))

    (dispose []
      (dispose-all @current-context))

    (render []
      (ScreenUtils/clear color/black)
      (let [context @current-context]
        (graphics/fix-viewport-update context)
        (screen/render (ctx/current-screen context) context)))

    (resize [w h]
      (graphics/update-viewports @current-context w h))))

(defn- lwjgl3-configuration [{:keys [title width height full-screen? fps]}]
  {:pre [title
         width
         height
         (boolean? full-screen?)
         (or (nil? fps) (int? fps))]}
  (let [config (doto (Lwjgl3ApplicationConfiguration.)
                 (.setTitle title)
                 (.setForegroundFPS (or fps 60)))]
    (if full-screen?
      (.setFullscreenMode config (Lwjgl3ApplicationConfiguration/getDisplayMode))
      (.setWindowedMode config width height))
    config))

(defn start
  "Required keys:
   {:app {:title \"gdl demo\"
          :width 800
          :height 600
          :full-screen? false}
    :context ...}
  "
  [config]
  (assert (:context config))
  (Lwjgl3Application. (->application config)
                      (lwjgl3-configuration (:app config))))
