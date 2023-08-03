(ns ^:no-doc gdl.assets
  (:require [gdl.app :as app]
            [gdl.files :as files])
  (:import com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.graphics.Texture))

(def ^:private folder "resources/") ; TODO these are classpath settings ?
(def ^:private sounds-folder "sounds/")
(def ^:private sound-files-extensions #{"wav"})
(def ^:private image-files-extensions #{"png" "bmp"})

(app/defmanaged ^:private ^:dispose ^AssetManager manager (AssetManager.))

(defn- load-assets [file-extensions ^Class class]
  (doseq [file (files/recursively-search-files folder file-extensions)]
    (app/log-debug "load-assets" (str "[" (.getSimpleName class) "] - [" file "]"))
    (.load manager file class)))

(defn- get-asset [file class] (.get manager ^String file ^Class class))

(defn ^Sound   get-sound   [file] (get-asset (str sounds-folder file) Sound))
(defn ^Texture get-texture [file] (get-asset                    file  Texture))

(app/on-create
 (load-assets sound-files-extensions Sound)
 (load-assets image-files-extensions Texture)
 (.finishLoading manager))

