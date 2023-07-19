(ns ^:no-doc gdx.assets
  (:require [gdx.app :as app]
            [gdx.files :as files])
  (:import com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.graphics.Texture))

(def ^:private folder "resources/")
(def ^:private sounds-folder "sounds/")
(def ^:private sound-files-extensions #{"wav"})
(def ^:private image-files-extensions #{"png" "bmp"})

(app/defmanaged ^:private ^:dispose ^AssetManager manager (AssetManager.))

(defn- load-assets [file-extensions klass]
  (doseq [file (files/recursively-search-files folder file-extensions)]
    (.debug app/app "gdx.assets" (str "load [" klass "] - [" file "]"))
    (.load manager file klass)))

(defn- get-asset [file klass]
  (.get manager ^String file ^Class klass))

(app/on-create
 (load-assets sound-files-extensions Sound)
 (load-assets image-files-extensions Texture)
 (.finishLoading manager))

(defn ^Sound get-sound [file]
  (get-asset (str sounds-folder file) Sound))

(defn ^Texture get-texture [file]
  (get-asset file Texture))
