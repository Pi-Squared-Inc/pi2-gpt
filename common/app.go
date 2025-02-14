package common

import (
	"net/http"

	"github.com/Khan/genqlient/graphql"
)

type App struct {
	StrapiUrl    string
	StrapiApiKey string
	Client       *graphql.Client
}

type authedTransport struct {
	wrapped http.RoundTripper
	apiKey  string
}

func (t *authedTransport) RoundTrip(req *http.Request) (*http.Response, error) {
	req.Header.Set("Authorization", "bearer "+t.apiKey)
	return t.wrapped.RoundTrip(req)
}

func NewApp(strapiUrl, strapiApiKey string) *App {
	client := graphql.NewClient(strapiUrl, &http.Client{
		Transport: &authedTransport{
			wrapped: http.DefaultTransport,
			apiKey:  strapiApiKey,
		},
	})

	return &App{
		StrapiUrl:    strapiUrl,
		StrapiApiKey: strapiApiKey,
		Client:       &client,
	}
}
