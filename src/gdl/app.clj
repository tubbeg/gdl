(ns gdl.app
  (:require [clojure.string :as str]
            [gdl.screen :as screen]
            [gdl.protocols :refer [dispose]]
            gdl.context.image-drawer-creator
            gdl.context.shape-drawer
            gdl.context.text-drawer
            gdl.context.ttf-generator
            gdl.context.gui-world-views
            gdl.scene2d.ui)
  (:import (com.badlogic.gdx Gdx ApplicationAdapter)
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.assets.AssetManager
           (com.badlogic.gdx.backends.lwjgl3 Lwjgl3Application Lwjgl3ApplicationConfiguration)
           com.badlogic.gdx.files.FileHandle
           (com.badlogic.gdx.graphics Color Texture)
           com.badlogic.gdx.graphics.g2d.SpriteBatch
           com.badlogic.gdx.utils.ScreenUtils))

; I could do extend-type in a function (is possible?)
; and call it explitly and also check if I have all the context ingredients necessary
; ( but they are only needed at runtime? e.g. drawer ?)


(defn- recursively-search-files [folder extensions]
  (loop [[^FileHandle file & remaining] (.list (.internal Gdx/files folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file) (recur (concat remaining (.list file)) result)
          (extensions (.extension file)) (recur remaining (conj result (str/replace-first (.path file) folder "")))
          :else (recur remaining result))))

(defn- load-assets [^AssetManager manager folder file-extensions ^Class klass log-load-assets?]
  (doseq [file (recursively-search-files folder file-extensions)]
    (when log-load-assets?
      (println "load-assets" (str "[" (.getSimpleName klass) "] - [" file "]")))
    (.load manager file klass)))

(defn- load-all-assets [{:keys [folder
                                log-load-assets?
                                sound-files-extensions
                                image-files-extensions]
                         :as config}]
  (doseq [k [:folder
             :log-load-assets?
             :sound-files-extensions
             :image-files-extensions]]
    (assert (contains? config k)
            (str "config key(s) missing: " k)))
  (let [manager (proxy [AssetManager clojure.lang.ILookup] []
                  (valAt [file]
                    (.get ^AssetManager this ^String file)))]
    (load-assets manager folder sound-files-extensions Sound   log-load-assets?)
    (load-assets manager folder image-files-extensions Texture log-load-assets?)
    (.finishLoading manager)
    manager))

; TODO ! all keywords add namespace ':context/' or something else

(defn- default-components [{:keys [tile-size]}]
  (let [batch (SpriteBatch.)]
    (merge {:batch batch
            :assets (load-all-assets {:folder "resources/" ; TODO these are classpath settings ?
                                      :sound-files-extensions #{"wav"}
                                      :image-files-extensions #{"png" "bmp"}
                                      :log-load-assets? false})
            :context/scene2d.ui (gdl.scene2d.ui/initialize!)}
           (gdl.context.text-drawer/->context-map)
           (gdl.context.shape-drawer/->context-map batch)
           (gdl.context.gui-world-views/->context-map :tile-size tile-size))))


(def state (atom nil)) ; TODO rename context?

(defn current-context []
  (gdl.protocols/assoc-view-mouse-positions @state))

; TODO here not current-context .... should not do @state or get mouse-positions via function call
; but then keep unprojecting ?
; TODO TEST current logic of that screen will be continued ?
(defn change-screen! [new-screen-key]
  (let [{:keys [context/current-screen] :as context} @state]
    (when-let [previous-screen (get context current-screen)]
      (screen/hide previous-screen context))
    (let [new-screen (new-screen-key context)]
      (assert new-screen (str "Cannot find screen with key: " new-screen-key))
      (swap! state assoc :context/current-screen new-screen-key)
      (screen/show new-screen @state))))

(defn- dispose-context [context]
  (doseq [[k value] context]
    (cond (extends? gdl.protocols/Disposable (class value))
          (do
           (println "Disposing " k)
           (dispose value))
          ((supers (class value)) com.badlogic.gdx.utils.Disposable)
          (do
           (println "Disposing " k)
           (.dispose ^com.badlogic.gdx.utils.Disposable value)))))

(defn- application-adapter [{:keys [modules first-screen] :as config}]
  (proxy [ApplicationAdapter] []
    (create []
      ; TODO let completely the user do this
      (let [context (-> config
                        default-components
                        gdl.protocols/map->Context)
            context (merge context (modules context))]  ; TODO safe-merge ?
        (reset! state context))
      (change-screen! first-screen))
    (dispose []
      (dispose-context @state))
    (render []
      (ScreenUtils/clear Color/BLACK)
      (let [{:keys [context/current-screen] :as context} (current-context)
            screen (current-screen context)]

        ; "Sometimes the viewport update is not triggered."
        ; TODO (on mac osx, when resizing window, make bug report, fix it in libgdx?)
        (gdl.protocols/fix-viewport-update context)
        (screen/render screen context)
        (screen/tick screen context (* (.getDeltaTime Gdx/graphics) 1000))))
    (resize [w h]
      ; TODO here also @state and not current-context ...
      (gdl.protocols/update-viewports @state w h))))

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

(defn start [config]
  (Lwjgl3Application. (application-adapter config)
                      (lwjgl3-configuration (:app config))))
