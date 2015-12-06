var gulp = require('gulp'),
    //autoprefixer = require('gulp-autoprefixer'),
    //minifycss = require('gulp-minify-css'),
    jshint = require('gulp-jshint'),
    //uglify = require('gulp-uglify'),
    //imagemin = require('gulp-imagemin'),
    //rename = require('gulp-rename'),
    //concat = require('gulp-concat'),
    //notify = require('gulp-notify'),
    cache = require('gulp-cache'),
    //livereload = require('gulp-livereload'),
    del = require('del');

gulp.task('default', function() {
    console.log('gulp task [default] ...')
});

gulp.task('jshint', function() {

});

gulp.task('clear', function (done) {
    return cache.clearAll(done);
});