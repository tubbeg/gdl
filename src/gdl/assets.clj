(ns gdl.assets
  (:require [x.x :refer [defmodule]]
            [gdl.lc :as lc]
            [gdl.files :as files])
  (:import com.badlogic.gdx.assets.AssetManager
           com.badlogic.gdx.audio.Sound
           com.badlogic.gdx.graphics.Texture))

(declare ^:private ^AssetManager manager
         ^:private sounds-folder)

(defn- load-assets [folder file-extensions ^Class klass log-load-assets?]
  (doseq [file (files/recursively-search-files folder file-extensions)]
    (when log-load-assets?
      (println "load-assets" (str "[" (.getSimpleName klass) "] - [" file "]")))
    (.load manager file klass)))

(defn- check-config [config]
  (doseq [k [:folder
             :sounds-folder
             :log-load-assets?
             :sound-files-extensions
             :image-files-extensions]]
    (assert (contains? config k)
            (str "config key(s) missing: " k))))

(defmodule {:keys [folder
                   sounds-folder
                   log-load-assets?
                   sound-files-extensions
                   image-files-extensions]
            :as config}
  (lc/create [_]
    (check-config config)
    (.bindRoot #'manager (AssetManager.))
    (.bindRoot #'sounds-folder sounds-folder)
    (load-assets folder sound-files-extensions Sound   log-load-assets?)
    (load-assets folder image-files-extensions Texture log-load-assets?)
    (.finishLoading manager))
  (lc/dispose [_]
    (.dispose manager)))

(defn- get-asset [file klass]
  (.get manager ^String file ^Class klass))

(defn ^Sound get-sound [file]
  (get-asset (str sounds-folder file) Sound))

(defn ^Texture get-texture [file]
  (get-asset file Texture))


