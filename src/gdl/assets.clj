(ns gdl.assets
  (:require [gdl.app :refer [log-debug]]
            [gdl.files :as files])
  (:import com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.graphics.Texture))

(declare ^AssetManager manager)

(defn asset-manager []
  (AssetManager.))

(defn- load-asset [file class]
  (.load manager file class))

(defn- finish-loading []
  (.finishLoading manager))

(defn- get-asset [file class]
  (.get manager ^String file ^Class class))

(defn- load-assets [folder file-extensions ^Class class]
  (doseq [file (files/recursively-search-files folder file-extensions)]
    ; TODO
    (println "load-assets" (str "[" (.getSimpleName class) "] - [" file "]"))
    (load-asset file class)))

(defn load-all [{:keys [folder
                        sound-files-extensions
                        image-files-extensions]}]
 (load-assets folder sound-files-extensions Sound)
 (load-assets folder image-files-extensions Texture)
 (finish-loading))

(declare sounds-folder)

(defn ^Sound   get-sound   [file] (get-asset (str sounds-folder file) Sound))
(defn ^Texture get-texture [file] (get-asset                    file  Texture))
