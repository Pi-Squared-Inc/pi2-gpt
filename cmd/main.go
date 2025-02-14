package main

import (
	"scraper/scripts"
	"os"
	"github.com/joho/godotenv"
	"scraper/common"
)

func main() {
	godotenv.Load()

	strapiUrl := os.Getenv("STRAPI_URL")
	strapiApiKey := os.Getenv("STRAPI_API_KEY")

	app := common.NewApp(strapiUrl, strapiApiKey)
	scripts.ScrapeTeamMembers(app)
	scripts.ScrapeEvents(app)
}
