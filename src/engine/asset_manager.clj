
; TODO
; memoized get-sound and file->texture  -> memoize on-create (better)
; rename get-sound to file->sound
; recursively search only once

; TODO private namespace for engine itself, no need to use it outside
; -> how to achieve this ?
; -> also graphics on-create/on-dispose ? (should be private ?!)
; load in different files internal code ?
; or use no-doc for generated code

; different files & all exposed as damn.engine or something like that ?

(ns engine.asset-manager
  (:require [clojure.string :as str]
            [engine.utils :refer (set-var-root)])
  (:import [com.badlogic.gdx Gdx]
           [com.badlogic.gdx.assets AssetManager]
           [com.badlogic.gdx.audio Sound]
           [com.badlogic.gdx.graphics Texture]
           [com.badlogic.gdx.graphics.g2d TextureRegion]))

(defn- recursively-search-files [folder extensions]
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

(defn- load-sounds [assets-folder]
  (let [sounds (recursively-search-files assets-folder #{"wav"})]
    #_(println "Found" (count sounds) "sounds.") ; TODO logging all println
    (dorun (map #(.load asset-manager % Sound) sounds)))
  #_(println "Loading all sounds...")
  (.finishLoading asset-manager))

(defn- load-images [assets-folder]
  (.load asset-manager "simple_6x8.png" Texture) ; loaded separately because its the only engine specific resource

  (let [images (recursively-search-files assets-folder #{"png" "bmp"})]
    #_(println "Found" (count images) "images.")
    (dorun (map #(.load asset-manager % Texture) images)))

  #_(println "Loading all images ...")
  (.finishLoading asset-manager))

(def get-sound
  (memoize
   (fn [spath]
     (.get asset-manager (str "sounds/" spath) Sound))))

; Here alternatively use GradientSprite instead of TextureRegion to apply color all
; corners of a sprite.
(def file->texture
  (memoize
   (fn [file & [x y w h]]
     (let [^Texture texture (.get asset-manager ^String file ^Class Texture)]
       (if (and x y w h)
         (TextureRegion. texture (int x) (int y) (int w) (int h))
         (TextureRegion. texture))))))

(defn on-create [assets-folder]
  (set-var-root #'asset-manager (AssetManager.))
  (load-sounds assets-folder)
  (load-images assets-folder))

(defn on-dispose []
  (.dispose asset-manager))
