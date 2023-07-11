(ns gdx.asset-manager
  (:require [clojure.string :as str]
            [gdx.app :as app]
            [gdx.utils :refer (set-var-root)])
  (:import [com.badlogic.gdx Gdx]
           [com.badlogic.gdx.assets AssetManager]
           [com.badlogic.gdx.audio Sound]
           [com.badlogic.gdx.graphics Texture]
           [com.badlogic.gdx.graphics.g2d TextureRegion]))

(def ^:private folder "resources/")

; TODO to utils?
(defn- recursively-search-files [extensions]
  (loop [[file & remaining] (.list (.internal (Gdx/files) folder))
         result []]
    (cond (nil? file) result
          (.isDirectory file)
          (recur (concat remaining (.list file)) result)
          (extensions (.extension file))
          (recur remaining (conj result (str/replace (.path file) folder "")))
          :else
          (recur remaining result))))

(declare ^:private ^AssetManager asset-manager)

(defn- load-sounds []
  (let [sounds (recursively-search-files #{"wav"})]
    #_(println "Found" (count sounds) "sounds.") ; TODO logging all println
    (dorun (map #(.load asset-manager % Sound) sounds)))
  #_(println "Loading all sounds...")
  (.finishLoading asset-manager))

(defn- load-images []
  (.load asset-manager "simple_6x8.png" Texture) ; loaded separately because its the only engine specific resource

  (let [images (recursively-search-files #{"png" "bmp"})]
    #_(println "Found" (count images) "images.")
    (dorun (map #(.load asset-manager % Texture) images)))

  #_(println "Loading all images ...")
  (.finishLoading asset-manager))

(declare file->sound
         file->texture)

(app/on-create
 (set-var-root #'asset-manager (AssetManager.))

 ; TODO type hint
 (set-var-root #'file->sound
   (memoize
    (fn [spath]
      (.get asset-manager (str "sounds/" spath) Sound))))

 ; TODO type hint
 (set-var-root #'file->texture
   (memoize
    (fn [file & [x y w h]]
      (let [^Texture texture (.get asset-manager ^String file ^Class Texture)]
        (if (and x y w h)
          (TextureRegion. texture (int x) (int y) (int w) (int h))
          (TextureRegion. texture))))))

 (load-sounds)
 (load-images))

(app/on-destroy
 (.dispose asset-manager))
