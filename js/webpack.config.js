module.exports = {
  entry: {
    main: './index.ts'
  },
  resolve: {
    extensions: ['.tsx', '.ts', '.js'],
  },
  output: {
    path: __dirname + '/dist',
    filename: "spaik-repl.bundle.js"
  },
  module: {
    rules: [
      // { test: /\.js$/,   exclude: /node_modules/, loader: "babel-loader" },
      { test: /\.tsx?$/, exclude: /node_modules/, loader: "ts-loader"    },
    ]
  },
  devtool: "source-map"
  // plugins: []
};
