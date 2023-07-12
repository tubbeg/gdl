; TODO
; loads synchronously on app start all pngs,bmps and wav files in resources/
; asset-manager disposes automatically on app destroy of all resources
(ns gdx.asset-manager
  (:require [gdx.utils :refer (set-var-root)]
            [gdx.app :as app]
            [gdx.files :as files])
  (:import [com.badlogic.gdx.assets AssetManager]
           [com.badlogic.gdx.audio Sound]
           [com.badlogic.gdx.graphics Texture]
           [com.badlogic.gdx.graphics.g2d TextureRegion]))

(def ^:private assets-folder "resources/")
(def ^:private sounds-subfolder "sounds/")
(def ^:private sound-files-extensions #{"wav"})
(def ^:private image-files-extensions #{"png" "bmp"})

(declare ^{:private true :tag AssetManager} asset-manager)

(app/on-create
 (set-var-root #'asset-manager (AssetManager.)))

(app/on-destroy
 (.dispose asset-manager))

(defn- load-sounds []
  (doseq [file (files/recursively-search-files assets-folder sound-files-extensions)]
    (.load asset-manager file Sound)))

(defn- load-images []
  (doseq [file (files/recursively-search-files assets-folder image-files-extensions)]
    (.load asset-manager file Texture)))

 ; TODO type hint here or @ play? <- here !?
 ; TODO type hint inside hashmap possible ? only symbol names ?
(declare ^Sound file->sound
         file->texture)

(app/on-create
 ; TODO remove.
 (.load asset-manager "simple_6x8.png" Texture) ; loaded separately because its the only engine specific resource

 (load-sounds)
 (load-images)
 (.finishLoading asset-manager)

 (set-var-root #'file->sound
   (memoize
    (fn [file]
      (.get asset-manager (str sounds-subfolder file) Sound))))

 (set-var-root #'file->texture
   (memoize
    (fn [file & [x y w h]]
      (let [^Texture texture (.get asset-manager ^String file ^Class Texture)]
        (if (and x y w h)
          (TextureRegion. texture (int x) (int y) (int w) (int h))
          (TextureRegion. texture)))))))
